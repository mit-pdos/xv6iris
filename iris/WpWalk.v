(* WpWalk.v -- the whole-function WP for xv6's walk() (kernel/vm.c): the
   3-level Sv39 page-table walk with allocation, proved ONCE over the
   abstract translation regime [R : s_regime] (boot instantiates
   [bare_regime], the user-table callers [kpt_regime kroot]).

   Spec of record: KvmSpec.v's [walk_spec] (this lemma concludes it).
   Decode catalog: WpWalkInstr.v (the wi_* facts; its header holds the
   instruction table and path structure).  Pure/Iris substrate:
   PtBuild.v (pt_rep0 / grafting / the address-arithmetic bridges /
   the V-bit dichotomy) and the ptree accessors (PtTree.v + PtBuild §5).

   PATH STRUCTURE (premises kill the panic arm [va < 2^38] and the
   alloc=0 arm [a2 = 1]): the two unrolled loop iterations each either
   DESCEND (slot V=1) or ALLOCATE (kalloc + memset + pointer-PTE store),
   and kalloc's null return exits through the shared epilogue with
   a0 = 0.  [pt_rep0 t m]'s per-vpn totality drives the branch:
     m !! vpn = Some w  ->  maps: descend, descend, w0 = the leaf word;
     None + blocks0 arm 1 -> graft2 {null-exit}, graft1 {null-exit};
     None + arm 2         -> descend, graft1 {null-exit};
     None + arm 3         -> descend, descend, w0 = 0.                  *)
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
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText WpAuipc.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SRegime.
Require Import SmodeCore WpSmodeGpr.
Require Import WpMycpu.
Require Import WpLock.
Require Import WpKalloc WpMemsetPage.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv.
Require Import SmodePte Pt4kWalk CommonWalk PtAdBits PtTree PtTreeAdue KptTree SmodeCorePt.
Require Import PtBuild KvmSpec.
Require Import WpSmodePtLeaves WpSmodePtAlu WpSmodePtBtype WpSmodePtCtl.
Require Import WpSmodePtMem WpSmodePtMemWrap.
Require Import WpWalkInstr UserBits.
Require Export WpSmodeLeafBase.
From Kernel Require KernelSyms.
Import Defs.

Section Walk.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation WK := KernelSyms.walk.

  (* the +64/-64 c.addi16sp frame cancel (walk's frame; clone of
     WpWakeup's wakeup_sp_cancel -- a whole-function file we do not
     import) *)
  Lemma walk_sp_cancel (X : mword 64) :
    add_vec (add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))
            (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = X.
  Proof.
    assert (add_vec_unsigned : forall x y : mword 64,
              bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
    { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
        SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
      rewrite bv_add_unsigned. reflexivity. }
    apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
    assert (HA : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)) : mword 64) = 18446744073709551552) by (vm_compute; reflexivity).
    assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)) : mword 64) = 64) by (vm_compute; reflexivity).
    rewrite HA HB. rewrite <- Z.add_assoc.
    replace (18446744073709551552 + 64) with (bv_modulus 64) by (vm_compute; reflexivity).
    rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
  Qed.

  Lemma wp_walk_r (R : s_regime) (Φ : mval -> iProp Σ)
      (γ : gname) (γc : gname) (bsie : mword 1)
      (mm : gmap regidx (mword 64)) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (n : nat) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (22 <= n)%nat ->
    mm !!! Regidx (mword_of_int 10)
      = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
    mm !!! Regidx (mword_of_int 12) = mword_of_int 1 ->
    (uint va < 2 ^ 38)%Z ->
    pt_rep0 t m ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
    sr_inv R -∗ kernel_text -∗
    pc_is (mword_of_int WK) -∗
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
      ⌜ptree_same_rep0 t t'⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
        \/ (exists p2 p1 w0,
             ptree_level0 t' vpn p2 p1 w0 /\
             mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va vpn sp0 ret_tgt Hn Ha0 Ha2 Hva Hrep.
    (* the entry map after the prologue: W1 (sp) .. W9 (s5) *)
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    iIntros "Hcfg Htoken Htlbinv #Htext Hpc Hfile Hstk Hptree Henv Hcont".
    (* ---- peel walk's own 8-slot frame [spr, sp0) ---- *)
    iDestruct (stack_own_split_1 sp0 8 n ltac:(lia) with "Hstk") as "[Htop Hdeep]".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Htop".
    iDestruct "Htop" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _)".
    iDestruct "S1" as (v56) "Hc56". iDestruct "S2" as (v48) "Hc48".
    iDestruct "S3" as (v40) "Hc40". iDestruct "S4" as (v32) "Hc32".
    iDestruct "S5" as (v24) "Hc24". iDestruct "S6" as (v16) "Hc16".
    iDestruct "S7" as (v08) "Hc08". iDestruct "S8" as (v00) "Hc00".
    (* slot-address bridges: spr + 8u = pa_stk sp0 (8-u) *)
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 8 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite Hsprstk) in "Hdeep".
    (* the catalog facts for the prologue *)
    iPoseProof (wi_00 with "Htext") as "Hi00".
    iPoseProof (wi_02 with "Htext") as "Hi02".
    iPoseProof (wi_04 with "Htext") as "Hi04".
    iPoseProof (wi_06 with "Htext") as "Hi06".
    iPoseProof (wi_08 with "Htext") as "Hi08".
    iPoseProof (wi_0a with "Htext") as "Hi0a".
    iPoseProof (wi_0c with "Htext") as "Hi0c".
    iPoseProof (wi_0e with "Htext") as "Hi0e".
    iPoseProof (wi_10 with "Htext") as "Hi10".
    iPoseProof (wi_12 with "Htext") as "Hi12".
    iPoseProof (wi_14 with "Htext") as "Hi14".
    iPoseProof (wi_16 with "Htext") as "Hi16".
    iPoseProof (wi_18 with "Htext") as "Hi18".
    iPoseProof (wi_1a with "Htext") as "Hi1a".
    iPoseProof (wi_1c with "Htext") as "Hi1c".
    iPoseProof (wi_1e with "Htext") as "Hi1e".
    iPoseProof (wi_20 with "Htext") as "Hi20".
    iPoseProof (wi_22 with "Htext") as "Hi22".
    (* +0x00 c.addi16sp sp,-64 *)
    iApply (wp_caddi16sp_gpr_s_r R γc Φ (mword_of_int WK) (mword_of_int 60 : mword 6) mm 1%Qp
              with "Hcfg Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> mm).
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr)
      by (rewrite /W1; rewrite lookup_total_insert; reflexivity).
    assert (Hpp02 : add_vec_int (mword_of_int WK : mword 64) 2 = mword_of_int (WK + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp x1,56(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x02)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
              W1 v56 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi02 [Hc56] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc56". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc56".
    assert (Hpp04 : add_vec_int (mword_of_int (WK + 0x02) : mword 64) 2 = mword_of_int (WK + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp x8,48(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x04)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              W1 v48 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi04 [Hc48] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc48". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc48".
    assert (Hpp06 : add_vec_int (mword_of_int (WK + 0x04) : mword 64) 2 = mword_of_int (WK + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp x9,40(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x06)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              W1 v40 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi06 [Hc40] [-]").
    { iEval (rewrite HspW1 Hb3). iExact "Hc40". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc40".
    assert (Hpp08 : add_vec_int (mword_of_int (WK + 0x06) : mword 64) 2 = mword_of_int (WK + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp x18,32(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x08)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              W1 v32 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi08 [Hc32] [-]").
    { iEval (rewrite HspW1 Hb4). iExact "Hc32". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc32".
    assert (Hpp0a : add_vec_int (mword_of_int (WK + 0x08) : mword 64) 2 = mword_of_int (WK + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp x19,24(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x0a)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              W1 v24 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi0a [Hc24] [-]").
    { iEval (rewrite HspW1 Hb5). iExact "Hc24". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc24".
    assert (Hpp0c : add_vec_int (mword_of_int (WK + 0x0a) : mword 64) 2 = mword_of_int (WK + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.sdsp x20,16(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x0c)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              W1 v16 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi0c [Hc16] [-]").
    { iEval (rewrite HspW1 Hb6). iExact "Hc16". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc16".
    assert (Hpp0e : add_vec_int (mword_of_int (WK + 0x0c) : mword 64) 2 = mword_of_int (WK + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.sdsp x21,8(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x0e)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              W1 v08 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi0e [Hc08] [-]").
    { iEval (rewrite HspW1 Hb7). iExact "Hc08". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc08".
    assert (Hpp10 : add_vec_int (mword_of_int (WK + 0x0e) : mword 64) 2 = mword_of_int (WK + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.sdsp x22,0(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x10)) (mword_of_int 0 : mword 6) (mword_of_int 22 : mword 5)
              W1 v00 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi10 [Hc00] [-]").
    { iEval (rewrite HspW1 Hb8). iExact "Hc00". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc00".
    assert (Hpp12 : add_vec_int (mword_of_int (WK + 0x10) : mword 64) 2 = mword_of_int (WK + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.addi4spn s0,sp,64 *)
    iApply (wp_caddi4spn_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x12)) (Cregidx (mword_of_int 0)) (mword_of_int 16 : mword 8) (mword_of_int 8 : mword 5)
              W1 (dq:=DfracOwn 1)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> W1).
    assert (Hpp14 : add_vec_int (mword_of_int (WK + 0x12) : mword 64) 2 = mword_of_int (WK + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.mv x9,x10 *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x14)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              W2 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi14 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (W2 !!! Regidx (mword_of_int 10 : mword 5)))]> W2).
    assert (Hpp16 : add_vec_int (mword_of_int (WK + 0x14) : mword 64) 2 = mword_of_int (WK + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 c.mv x19,x11 *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x16)) (mword_of_int 19 : mword 5) (mword_of_int 11 : mword 5)
              W3 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W4 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg
        (add_vec zero_reg (W3 !!! Regidx (mword_of_int 11 : mword 5)))]> W3).
    assert (Hpp18 : add_vec_int (mword_of_int (WK + 0x16) : mword 64) 2 = mword_of_int (WK + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.mv x22,x12 *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x18)) (mword_of_int 22 : mword 5) (mword_of_int 12 : mword 5)
              W4 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi18 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W5 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg
        (add_vec zero_reg (W4 !!! Regidx (mword_of_int 12 : mword 5)))]> W4).
    assert (Hpp1a : add_vec_int (mword_of_int (WK + 0x18) : mword 64) 2 = mword_of_int (WK + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.li a5,-1 *)
    iApply (wp_cli_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 63 : mword 6)
              W5 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi1a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> W5).
    assert (Hpp1c : add_vec_int (mword_of_int (WK + 0x1a) : mword 64) 2 = mword_of_int (WK + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.srli a5,26 *)
    iApply (wp_csrli_s_r R γc Φ (mword_of_int (WK + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 26 : mword 6)
              (shift_bits_right (W6 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 26 : mword 6) (Z.sub log2_xlen 1) 0))
              W6 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi1c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (W6 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 26 : mword 6) (Z.sub log2_xlen 1) 0))]> W6).
    assert (Hpp1e : add_vec_int (mword_of_int (WK + 0x1c) : mword 64) 2 = mword_of_int (WK + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.li s4,30 *)
    iApply (wp_cli_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x1e)) (mword_of_int 20 : mword 5) (mword_of_int 30 : mword 6)
              W7 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi1e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W8 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 30 : mword 6))))]> W7).
    assert (Hpp20 : add_vec_int (mword_of_int (WK + 0x1e) : mword 64) 2 = mword_of_int (WK + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 c.li s5,12 *)
    iApply (wp_cli_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x20)) (mword_of_int 21 : mword 5) (mword_of_int 12 : mword 6)
              W8 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi20 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W9 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 12 : mword 6))))]> W8).
    assert (Hpp22 : add_vec_int (mword_of_int (WK + 0x20) : mword 64) 2 = mword_of_int (WK + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* the register-value facts the loop needs *)
    assert (Hva' : uint va < 274877906944) by (change 274877906944 with (2 ^ 38); exact Hva).
    assert (HW9va : W9 !!! Regidx (mword_of_int 11 : mword 5) = va).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      reflexivity. }
    assert (HW6a5 : W6 !!! Regidx (mword_of_int 15 : mword 5)
                    = (mword_of_int 18446744073709551615 : mword 64)).
    { rewrite /W6 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    assert (HW9a5 : W9 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 274877906943).
    { rewrite /W9 /W8.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite /W7 lookup_total_insert. rewrite HW6a5.
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x22 bltu a5,a1 FALLS: va <= MAXVA-1 *)
    iApply (wp_bltu_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x22)) (mword_of_int 68 : mword 13) (mword_of_int 11 : mword 5) (mword_of_int 15 : mword 5)
              W9 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HW9a5 HW9va; unfold zopz0zI_u; apply Z.ltb_ge;
                    replace (uint (mword_of_int 274877906943 : mword 64)) with 274877906943 by (vm_compute; reflexivity);
                    lia)
              with "Hcfg Htlbinv Hpc Hfile Hi22 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp26 : add_vec_int (mword_of_int (WK + 0x22) : mword 64) 4 = mword_of_int (WK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* ================= LOOP ITERATION 1 (s4 = 30, level 2) ============ *)
    iPoseProof (wi_26 with "Htext") as "Hi26".
    iPoseProof (wi_2a with "Htext") as "Hi2a".
    iPoseProof (wi_2e with "Htext") as "Hi2e".
    iPoseProof (wi_30 with "Htext") as "Hi30".
    iPoseProof (wi_32 with "Htext") as "Hi32".
    iPoseProof (wi_36 with "Htext") as "Hi36".
    iPoseProof (wi_3a with "Htext") as "Hi3a".
    assert (HW9s3 : W9 !!! Regidx (mword_of_int 19 : mword 5) = va).
    { rewrite /W9 /W8 /W7 /W6 /W5.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite /W4 lookup_total_insert.
      rewrite /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite add_vec_zero_l. reflexivity. }
    assert (HW9s4 : W9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
    { rewrite /W9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /W8 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    assert (HW9s1 : W9 !!! Regidx (mword_of_int 9 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite /W3 lookup_total_insert.
      rewrite /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite add_vec_zero_l. rewrite Ha0. reflexivity. }
    (* +0x26 srl s2,s3,s4 *)
    iApply (wp_srl_s_r R γc Φ (mword_of_int (WK + 0x26)) (mword_of_int 18 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 20 : mword 5)
              (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
              W9 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite HW9s3 HW9s4; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi26 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (L1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))]> W9).
    assert (Hpp2a : add_vec_int (mword_of_int (WK + 0x26) : mword 64) 4 = mword_of_int (WK + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a andi s2,s2,511 *)
    iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x2a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 511 : mword 12)
              (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
                       (sign_extend' 64 (mword_of_int 511 : mword 12)))
              L1 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /L1 lookup_total_insert; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi2a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (L2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (mword_of_int 511 : mword 12)))]> L1).
    assert (Hpp2e : add_vec_int (mword_of_int (WK + 0x2a) : mword 64) 4 = mword_of_int (WK + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.slli s2,3 *)
    iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x2e)) (mword_of_int 18 : mword 5) (mword_of_int 3 : mword 6)
              (shift_bits_left
                 (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
                          (sign_extend' 64 (mword_of_int 511 : mword 12)))
                 (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
              L2 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /L2 lookup_total_insert; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi2e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (L3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_left
           (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
                    (sign_extend' 64 (mword_of_int 511 : mword 12)))
           (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> L2).
    assert (Hpp30 : add_vec_int (mword_of_int (WK + 0x2e) : mword 64) 2 = mword_of_int (WK + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.add s2,s1 *)
    iApply (wp_cadd_s_scfg_r R γc Φ (mword_of_int (WK + 0x30)) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
              L3 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi30 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (L4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (add_vec (L3 !!! Regidx (mword_of_int 18 : mword 5)) (L3 !!! Regidx (mword_of_int 9 : mword 5)))]> L3).
    assert (Hpp32 : add_vec_int (mword_of_int (WK + 0x30) : mword 64) 2 = mword_of_int (WK + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* s2 now holds the ROOT slot address *)
    assert (HL3s1 : L3 !!! Regidx (mword_of_int 9 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite /L3 /L2 /L1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite lookup_total_insert.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite add_vec_zero_l. rewrite Ha0. reflexivity. }
    assert (HL4s2 : L4 !!! Regidx (mword_of_int 18 : mword 5)
                    = u_pte_addr (pt_base t) (vpn_idx 2 vpn)).
    { rewrite /L4 lookup_total_insert.
      rewrite {1}/L3 lookup_total_insert.
      rewrite HL3s1.
      exact (walk_slot_addr2 (pt_base t) va Hva').
    }
    (* the [sext 0] effective-address collapse for the ld/sd at 0(s2) *)
    assert (Hea0 : forall X : mword 64, add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* ---- +0x32 ld s1,0(s2): the slot read; [pt_rep0]'s totality drives
       the V-bit branch ---- *)
    destruct (m !! vpn) as [w|] eqn:Hmv.
    - (* ============ MAPPED vpn: descend, descend ============ *)
      destruct (proj1 Hrep vpn w Hmv) as (p2 & p1 & Hmaps).
      pose proof Hmaps as (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hch2 & Hch1 &
                           Hv2 & Hp2c & Hv1 & Hp1c & Hv0 & Hl0c & Hnap0 & Hpb0).
      iDestruct (ptree_own_slot2_ro (DfracOwn 1) t vpn with "Hptree") as "[Hslot Hcl2]".
      iApply (wp_ld_s_scfg_r R γc Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
                L4 (pt_ents t (vpn_idx 2 vpn)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi32 [Hslot] [-]").
      { iEval (rewrite Hea0 HL4s2). iExact "Hslot". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hslot".
      iEval (rewrite Hea0 HL4s2) in "Hslot".
      iDestruct ("Hcl2" with "Hslot") as "Hptree".
      set (L5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents t (vpn_idx 2 vpn))]> L4).
      assert (Hpp36 : add_vec_int (mword_of_int (WK + 0x32) : mword 64) 4 = mword_of_int (WK + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      (* +0x36 andi a5,s1,1 *)
      iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
                (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                L5 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /L5 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi36 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> L5).
      assert (Hpp3a : add_vec_int (mword_of_int (WK + 0x36) : mword 64) 4 = mword_of_int (WK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.beqz a5 FALLS: the mapped root slot has V = 1 *)
      assert (Hvbit2 : Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0 = true).
      { destruct (Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0) eqn:E;
          [reflexivity | exfalso].
        apply (pte_valid_invalid_excl (pt_ents t (vpn_idx 2 vpn))).
        - rewrite He2. exact Hv2.
        - exact (pte_invalid_bit0 _ E). }
      assert (HL6a5 : L6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /L6 lookup_total_insert; reflexivity).
      iApply (wp_cbeqz_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                L6 (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HL6a5 walk_vbit_eq Hvbit2; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpp3c : add_vec_int (mword_of_int (WK + 0x3a) : mword 64) 2 = mword_of_int (WK + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      (* +0x3c / +0x3e: the DESCEND -- s1 := (w >> 10) << 12 *)
      iPoseProof (wi_3c with "Htext") as "Hi3c".
      iPoseProof (wi_3e with "Htext") as "Hi3e".
      iPoseProof (wi_40 with "Htext") as "Hi40".
      iPoseProof (wi_42 with "Htext") as "Hi42".
      assert (HL6s1 : L6 !!! Regidx (mword_of_int 9 : mword 5) = pt_ents t (vpn_idx 2 vpn)).
      { rewrite /L6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /L5 lookup_total_insert. reflexivity. }
      iApply (wp_csrli_s_r R γc Φ (mword_of_int (WK + 0x3c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
                (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                L6 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HL6s1; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3c [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> L6).
      assert (Hpp3e : add_vec_int (mword_of_int (WK + 0x3c) : mword 64) 2 = mword_of_int (WK + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x3e)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
                (shift_bits_left
                   (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                   (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                L7 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /L7 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_left
             (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
             (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> L7).
      assert (Hpp40 : add_vec_int (mword_of_int (WK + 0x3e) : mword 64) 2 = mword_of_int (WK + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      (* the descended base: s1 = the level-1 node's page base *)
      assert (Hb1c : u_next_base (pt_ents t (vpn_idx 2 vpn)) = pt_base c1)
        by (rewrite He2; exact Hch2).
      assert (HL8s1 : L8 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /L8 lookup_total_insert.
        rewrite (walk_descend_base (pt_ents t (vpn_idx 2 vpn))
                   ltac:(rewrite He2; exact Hv2) ltac:(rewrite He2; exact Hp2c)).
        rewrite Hb1c. reflexivity. }
      (* +0x40 c.addiw s4,-9 : 30 -> 21 *)
      iApply (wp_caddiw_s_scfg_r R γc Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                L8 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (L8 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> L8).
      assert (Hpp42 : add_vec_int (mword_of_int (WK + 0x40) : mword 64) 2 = mword_of_int (WK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HL8s4 : L8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
      { rewrite /L8 /L7 /L6 /L5 /L4 /L3 /L2 /L1 /W9.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s4 : L9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /L9 lookup_total_insert. rewrite HL8s4.
        apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s5 : L9 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4 /L3 /L2 /L1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      (* +0x42 bne s4,s5 TAKEN (21 <> 12): back to +0x26 *)
      iApply (wp_bne_taken_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                L9 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HL9s4 HL9s5; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi42 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hbk26 : add_vec (mword_of_int (WK + 0x42) : mword 64) (sign_extend' 64 (mword_of_int 8164 : mword 13)) = mword_of_int (WK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbk26) in "Hpc".
      (* ================= LOOP ITERATION 2 (s4 = 21, level 1) ============ *)
      assert (HL9s3 : L9 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4 /L3 /L2 /L1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite add_vec_zero_l. reflexivity. }
      iApply (wp_srl_s_r R γc Φ (mword_of_int (WK + 0x26)) (mword_of_int 18 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 20 : mword 5)
                (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
                L9 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HL9s3 HL9s4; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi26 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))]> L9).
      iEval (rewrite Hpp2a) in "Hpc".
      iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x2a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 511 : mword 12)
                (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
                         (sign_extend' 64 (mword_of_int 511 : mword 12)))
                M1 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /M1 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi2a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
                   (sign_extend' 64 (mword_of_int 511 : mword 12)))]> M1).
      iEval (rewrite Hpp2e) in "Hpc".
      iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x2e)) (mword_of_int 18 : mword 5) (mword_of_int 3 : mword 6)
                (shift_bits_left
                   (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
                            (sign_extend' 64 (mword_of_int 511 : mword 12)))
                   (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
                M2 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /M2 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi2e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (shift_bits_left
             (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
                      (sign_extend' 64 (mword_of_int 511 : mword 12)))
             (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> M2).
      iEval (rewrite Hpp30) in "Hpc".
      iApply (wp_cadd_s_scfg_r R γc Φ (mword_of_int (WK + 0x30)) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
                M3 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi30 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (add_vec (M3 !!! Regidx (mword_of_int 18 : mword 5)) (M3 !!! Regidx (mword_of_int 9 : mword 5)))]> M3).
      iEval (rewrite Hpp32) in "Hpc".
      assert (HM3s1 : M3 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /M3 /M2 /M1 /L9.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        exact HL8s1. }
      assert (HM4s2 : M4 !!! Regidx (mword_of_int 18 : mword 5)
                      = u_pte_addr (pt_base c1) (vpn_idx 1 vpn)).
      { rewrite /M4 lookup_total_insert.
        rewrite {1}/M3 lookup_total_insert.
        rewrite HM3s1.
        exact (walk_slot_addr1 (pt_base c1) va Hva'). }
      (* +0x32 ld s1,0(s2): the L1 slot *)
      iDestruct (ptree_own_slot1_ro (DfracOwn 1) t c1 vpn Hk2 Hb1c with "Hptree") as "[Hslot1 Hcl1]".
      iApply (wp_ld_s_scfg_r R γc Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
                M4 (pt_ents c1 (vpn_idx 1 vpn)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi32 [Hslot1] [-]").
      { iEval (rewrite Hea0 HM4s2). iEval (rewrite /pt_addr1 Hb1c) in "Hslot1". iExact "Hslot1". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hslot1".
      iEval (rewrite Hea0 HM4s2) in "Hslot1".
      iEval (rewrite /pt_addr1 Hb1c) in "Hcl1".
      iDestruct ("Hcl1" with "Hslot1") as "Hptree".
      set (M5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents c1 (vpn_idx 1 vpn))]> M4).
      iEval (rewrite Hpp36) in "Hpc".
      (* +0x36 andi a5,s1,1 *)
      iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
                (and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                M5 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /M5 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi36 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> M5).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.beqz a5 FALLS: the mapped L1 slot has V = 1 *)
      assert (Hvbit1 : Z.testbit (bv_unsigned (pt_ents c1 (vpn_idx 1 vpn))) 0 = true).
      { destruct (Z.testbit (bv_unsigned (pt_ents c1 (vpn_idx 1 vpn))) 0) eqn:E;
          [reflexivity | exfalso].
        apply (pte_valid_invalid_excl (pt_ents c1 (vpn_idx 1 vpn))).
        - rewrite He1. exact Hv1.
        - exact (pte_invalid_bit0 _ E). }
      assert (HM6a5 : M6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /M6 lookup_total_insert; reflexivity).
      iApply (wp_cbeqz_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                M6 (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HM6a5 walk_vbit_eq Hvbit1; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      iEval (rewrite Hpp3c) in "Hpc".
      (* +0x3c / +0x3e: descend to the level-0 node *)
      assert (HM6s1 : M6 !!! Regidx (mword_of_int 9 : mword 5) = pt_ents c1 (vpn_idx 1 vpn)).
      { rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M5 lookup_total_insert. reflexivity. }
      iApply (wp_csrli_s_r R γc Φ (mword_of_int (WK + 0x3c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
                (shift_bits_right (pt_ents c1 (vpn_idx 1 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                M6 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HM6s1; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3c [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_right (pt_ents c1 (vpn_idx 1 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> M6).
      iEval (rewrite Hpp3e) in "Hpc".
      iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x3e)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
                (shift_bits_left
                   (shift_bits_right (pt_ents c1 (vpn_idx 1 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                   (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                M7 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /M7 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_left
             (shift_bits_right (pt_ents c1 (vpn_idx 1 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
             (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> M7).
      iEval (rewrite Hpp40) in "Hpc".
      assert (Hb0c : u_next_base (pt_ents c1 (vpn_idx 1 vpn)) = pt_base c0)
        by (rewrite He1; exact Hch1).
      assert (HM8s1 : M8 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c0) (zeros' 12 : mword 12))).
      { rewrite /M8 lookup_total_insert.
        rewrite (walk_descend_base (pt_ents c1 (vpn_idx 1 vpn))
                   ltac:(rewrite He1; exact Hv1) ltac:(rewrite He1; exact Hp1c)).
        rewrite Hb0c. reflexivity. }
      (* +0x40 c.addiw s4,-9 : 21 -> 12; +0x42 bne FALLS *)
      iApply (wp_caddiw_s_scfg_r R γc Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                M8 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (M8 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> M8).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HM8s4 : M8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        exact HL9s4. }
      assert (HM9s4 : M9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /M9 lookup_total_insert. rewrite HM8s4.
        apply bv_eq; vm_compute; reflexivity. }
      assert (HM9s5 : M9 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_bne_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                M9 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HM9s4 HM9s5; vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi42 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpp46 : add_vec_int (mword_of_int (WK + 0x42) : mword 64) 4 = mword_of_int (WK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* ================= TAIL: a0 := &L0 slot ============ *)
      iPoseProof (wi_46 with "Htext") as "Hi46".
      iPoseProof (wi_4a with "Htext") as "Hi4a".
      iPoseProof (wi_4e with "Htext") as "Hi4e".
      iPoseProof (wi_50 with "Htext") as "Hi50".
      assert (HM9s3 : M9 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite add_vec_zero_l. reflexivity. }
      (* +0x46 srli a0,s3,12 *)
      iApply (wp_srli4_s_scfg_r R γc Φ (mword_of_int (WK + 0x46)) (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 12 : mword 6)
                M9 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi46 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (T1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (shift_bits_right (M9 !!! Regidx (mword_of_int 19 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> M9).
      assert (Hpp4a : add_vec_int (mword_of_int (WK + 0x46) : mword 64) 4 = mword_of_int (WK + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      (* +0x4a andi a0,a0,511 *)
      iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x4a)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 511 : mword 12)
                (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                         (sign_extend' 64 (mword_of_int 511 : mword 12)))
                T1 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /T1 lookup_total_insert; rewrite HM9s3; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi4a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (T2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                   (sign_extend' 64 (mword_of_int 511 : mword 12)))]> T1).
      assert (Hpp4e : add_vec_int (mword_of_int (WK + 0x4a) : mword 64) 4 = mword_of_int (WK + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4e) in "Hpc".
      (* +0x4e c.slli a0,3 *)
      iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x4e)) (mword_of_int 10 : mword 5) (mword_of_int 3 : mword 6)
                (shift_bits_left
                   (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                            (sign_extend' 64 (mword_of_int 511 : mword 12)))
                   (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
                T2 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /T2 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi4e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (T3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (shift_bits_left
             (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                      (sign_extend' 64 (mword_of_int 511 : mword 12)))
             (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> T2).
      assert (Hpp50 : add_vec_int (mword_of_int (WK + 0x4e) : mword 64) 2 = mword_of_int (WK + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp50) in "Hpc".
      (* +0x50 c.add a0,s1 *)
      iApply (wp_cadd_s_scfg_r R γc Φ (mword_of_int (WK + 0x50)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                T3 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi50 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (T4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec (T3 !!! Regidx (mword_of_int 10 : mword 5)) (T3 !!! Regidx (mword_of_int 9 : mword 5)))]> T3).
      assert (Hpp52 : add_vec_int (mword_of_int (WK + 0x50) : mword 64) 2 = mword_of_int (WK + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp52) in "Hpc".
      assert (HT3s1 : T3 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c0) (zeros' 12 : mword 12))).
      { rewrite /T3 /T2 /T1 /M9.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        exact HM8s1. }
      assert (HT4a0 : T4 !!! Regidx (mword_of_int 10 : mword 5)
                      = u_pte_addr (pt_base c0) (vpn_idx 0 vpn)).
      { rewrite /T4 lookup_total_insert.
        rewrite {1}/T3 lookup_total_insert.
        rewrite HT3s1.
        replace (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
          with (subrange_vec_dec (mword_of_int 12 : mword 64) (Z.sub log2_xlen 1) 0)
          by (apply bv_eq; vm_compute; reflexivity).
        exact (walk_slot_addr0 (pt_base c0) va Hva'). }
      (* ================= EPILOGUE ============ *)
      iPoseProof (wi_52 with "Htext") as "Hi52".
      iPoseProof (wi_54 with "Htext") as "Hi54".
      iPoseProof (wi_56 with "Htext") as "Hi56".
      iPoseProof (wi_58 with "Htext") as "Hi58".
      iPoseProof (wi_5a with "Htext") as "Hi5a".
      iPoseProof (wi_5c with "Htext") as "Hi5c".
      iPoseProof (wi_5e with "Htext") as "Hi5e".
      iPoseProof (wi_60 with "Htext") as "Hi60".
      iPoseProof (wi_62 with "Htext") as "Hi62".
      iPoseProof (wi_64 with "Htext") as "Hi64".
      assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r1) in "Hc56".
      assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r8) in "Hc48".
      assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r9) in "Hc40".
      assert (HW1r18 : W1 !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r18) in "Hc32".
      assert (HW1r19 : W1 !!! Regidx (mword_of_int 19 : mword 5) = mm !!! Regidx (mword_of_int 19)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r19) in "Hc24".
      assert (HW1r20 : W1 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 20)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r20) in "Hc16".
      assert (HW1r21 : W1 !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 21)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r21) in "Hc08".
      assert (HW1r22 : W1 !!! Regidx (mword_of_int 22 : mword 5) = mm !!! Regidx (mword_of_int 22)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r22) in "Hc00".
      (* +0x52 c.ldsp x1,56(sp) *)
      assert (HspT4 : T4 !!! Regidx csp_rs1 = spr).
      { rewrite /T4.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x52)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
                T4 (mm !!! Regidx (mword_of_int 1 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi52 [Hc56] [-]").
      { iEval (rewrite HspW1 Hb1) in "Hc56". iEval (rewrite HspT4 Hb1). iExact "Hc56". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hc56".
      set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> T4).
      assert (Hpp52n : add_vec_int (mword_of_int (WK + 0x52) : mword 64) 2 = mword_of_int (WK + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp52n) in "Hpc".
      (* +0x54 c.ldsp x8,48(sp) *)
      assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
      { rewrite /E1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x54)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
                E1 (mm !!! Regidx (mword_of_int 8 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi54 [Hc48] [-]").
      { iEval (rewrite HspW1 Hb2) in "Hc48". iEval (rewrite HspE1 Hb2). iExact "Hc48". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hc48".
      set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
      assert (Hpp54n : add_vec_int (mword_of_int (WK + 0x54) : mword 64) 2 = mword_of_int (WK + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp54n) in "Hpc".
      (* +0x56 c.ldsp x9,40(sp) *)
      assert (HspE2 : E2 !!! Regidx csp_rs1 = spr).
      { rewrite /E2.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x56)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
                E2 (mm !!! Regidx (mword_of_int 9 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi56 [Hc40] [-]").
      { iEval (rewrite HspW1 Hb3) in "Hc40". iEval (rewrite HspE2 Hb3). iExact "Hc40". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hc40".
      set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
      assert (Hpp56n : add_vec_int (mword_of_int (WK + 0x56) : mword 64) 2 = mword_of_int (WK + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp56n) in "Hpc".
      (* +0x58 c.ldsp x18,32(sp) *)
      assert (HspE3 : E3 !!! Regidx csp_rs1 = spr).
      { rewrite /E3.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x58)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
                E3 (mm !!! Regidx (mword_of_int 18 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi58 [Hc32] [-]").
      { iEval (rewrite HspW1 Hb4) in "Hc32". iEval (rewrite HspE3 Hb4). iExact "Hc32". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hc32".
      set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 18 : mword 5))]> E3).
      assert (Hpp58n : add_vec_int (mword_of_int (WK + 0x58) : mword 64) 2 = mword_of_int (WK + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp58n) in "Hpc".
      (* +0x5a c.ldsp x19,24(sp) *)
      assert (HspE4 : E4 !!! Regidx csp_rs1 = spr).
      { rewrite /E4.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x5a)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
                E4 (mm !!! Regidx (mword_of_int 19 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi5a [Hc24] [-]").
      { iEval (rewrite HspW1 Hb5) in "Hc24". iEval (rewrite HspE4 Hb5). iExact "Hc24". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hc24".
      set (E5 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 19 : mword 5))]> E4).
      assert (Hpp5an : add_vec_int (mword_of_int (WK + 0x5a) : mword 64) 2 = mword_of_int (WK + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5an) in "Hpc".
      (* +0x5c c.ldsp x20,16(sp) *)
      assert (HspE5 : E5 !!! Regidx csp_rs1 = spr).
      { rewrite /E5.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x5c)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
                E5 (mm !!! Regidx (mword_of_int 20 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi5c [Hc16] [-]").
      { iEval (rewrite HspW1 Hb6) in "Hc16". iEval (rewrite HspE5 Hb6). iExact "Hc16". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hc16".
      set (E6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 20 : mword 5))]> E5).
      assert (Hpp5cn : add_vec_int (mword_of_int (WK + 0x5c) : mword 64) 2 = mword_of_int (WK + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5cn) in "Hpc".
      (* +0x5e c.ldsp x21,8(sp) *)
      assert (HspE6 : E6 !!! Regidx csp_rs1 = spr).
      { rewrite /E6.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x5e)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
                E6 (mm !!! Regidx (mword_of_int 21 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi5e [Hc08] [-]").
      { iEval (rewrite HspW1 Hb7) in "Hc08". iEval (rewrite HspE6 Hb7). iExact "Hc08". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hc08".
      set (E7 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 21 : mword 5))]> E6).
      assert (Hpp5en : add_vec_int (mword_of_int (WK + 0x5e) : mword 64) 2 = mword_of_int (WK + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5en) in "Hpc".
      (* +0x60 c.ldsp x22,0(sp) *)
      assert (HspE7 : E7 !!! Regidx csp_rs1 = spr).
      { rewrite /E7.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x60)) (mword_of_int 0 : mword 6) (mword_of_int 22 : mword 5)
                E7 (mm !!! Regidx (mword_of_int 22 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi60 [Hc00] [-]").
      { iEval (rewrite HspW1 Hb8) in "Hc00". iEval (rewrite HspE7 Hb8). iExact "Hc00". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hc00".
      set (E8 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 22 : mword 5))]> E7).
      assert (Hpp60n : add_vec_int (mword_of_int (WK + 0x60) : mword 64) 2 = mword_of_int (WK + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp60n) in "Hpc".
      (* +0x62 c.addi16sp sp,+64 *)
      iApply (wp_caddi16sp_gpr_s_r R γc Φ (mword_of_int (WK + 0x62)) (mword_of_int 4 : mword 6) E8 1%Qp
                with "Hcfg Htlbinv Hpc Hfile Hi62 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (E9 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E8).
      assert (Hpp64 : add_vec_int (mword_of_int (WK + 0x62) : mword 64) 2 = mword_of_int (WK + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp64) in "Hpc".
      (* the restored sp *)
      assert (HspE8 : E8 !!! Regidx csp_rs1 = spr).
      { rewrite /E8.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      assert (HspE9 : E9 !!! Regidx csp_rs1 = sp0).
      { rewrite /E9 lookup_total_insert. rewrite HspE8.
        unfold spr. apply walk_sp_cancel. }
      (* +0x64 ret *)
      assert (HE9ra : E9 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
      { rewrite /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      assert (Hrt : update_vec_dec (add_vec (E9 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0" : mword 1) = ret_tgt).
      { rewrite HE9ra.
        replace (sign_extend' 64 (zeros' 12) : mword 64) with (mword_of_int 0 : mword 64)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite kv_addv_zero. reflexivity. }
      iApply (wp_cret_s_zca_scfg_r R γc Φ (mword_of_int (WK + 0x64)) (mword_of_int 1 : mword 5) E9 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrt; exact (bit0_update0_64 (mm !!! Regidx (mword_of_int 1))))
                with "Hcfg Htlbinv Hpc Hfile Hi64 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      iEval (rewrite Hrt) in "Hpc".
      (* ---- rebundle the stack and conclude ---- *)
      iAssert (stack_own sp0 8)%I with "[Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00]" as "Htop".
      { iEval (rewrite stack_own_slots; cbn [seq]).
        iSplitL "Hc56". { iExists (mm !!! Regidx (mword_of_int 1)). iEval (rewrite HspT4 Hb1) in "Hc56". iExact "Hc56". }
        iSplitL "Hc48". { iExists (mm !!! Regidx (mword_of_int 8)). iEval (rewrite HspE1 Hb2) in "Hc48". iExact "Hc48". }
        iSplitL "Hc40". { iExists (mm !!! Regidx (mword_of_int 9)). iEval (rewrite HspE2 Hb3) in "Hc40". iExact "Hc40". }
        iSplitL "Hc32". { iExists (mm !!! Regidx (mword_of_int 18)). iEval (rewrite HspE3 Hb4) in "Hc32". iExact "Hc32". }
        iSplitL "Hc24". { iExists (mm !!! Regidx (mword_of_int 19)). iEval (rewrite HspE4 Hb5) in "Hc24". iExact "Hc24". }
        iSplitL "Hc16". { iExists (mm !!! Regidx (mword_of_int 20)). iEval (rewrite HspE5 Hb6) in "Hc16". iExact "Hc16". }
        iSplitL "Hc08". { iExists (mm !!! Regidx (mword_of_int 21)). iEval (rewrite HspE6 Hb7) in "Hc08". iExact "Hc08". }
        iSplitL "Hc00". { iExists (mm !!! Regidx (mword_of_int 22)). iEval (rewrite HspE7 Hb8) in "Hc00". iExact "Hc00". }
        done. }
      iEval (rewrite -Hsprstk) in "Hdeep".
      iDestruct (stack_own_split_2 sp0 8 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
      iApply ("Hcont" $! E9 t with "Hcfg Htoken Htlbinv Hpc Hfile Hstk Hptree Henv [%] [%] [%]").
      { (* callee_saved mm E9 *)
        unfold callee_saved.
        split.
        { rewrite /E9 lookup_total_insert. rewrite HspE8.
          unfold spr. apply walk_sp_cancel. }
        split.
        { (* tp: never written *)
          rewrite /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1 /T4 /T3 /T2 /T1
                  /M9 /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1
                  /L9 /L8 /L7 /L6 /L5 /L4 /L3 /L2 /L1
                  /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1.
          repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
          reflexivity. }
        split.
        { (* s0 = x8: restored *)
          rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /E8 /E7 /E6 /E5 /E4 /E3.
          repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
          rewrite lookup_total_insert. reflexivity. }
        split.
        { (* s1 = x9 *)
          rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /E8 /E7 /E6 /E5 /E4.
          repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
          rewrite lookup_total_insert. reflexivity. }
        split.
        { (* s2 = x18 *)
          rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /E8 /E7 /E6 /E5.
          repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
          rewrite lookup_total_insert. reflexivity. }
        split.
        { (* s3 = x19 *)
          rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /E8 /E7 /E6.
          repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
          rewrite lookup_total_insert. reflexivity. }
        split.
        { (* s4 = x20 *)
          rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /E8 /E7.
          repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
          rewrite lookup_total_insert. reflexivity. }
        split.
        { (* s5 = x21 *)
          rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /E8.
          repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
          rewrite lookup_total_insert. reflexivity. }
        split.
        { (* s6 = x22 *)
          rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /E8 lookup_total_insert. reflexivity. }
        (* s7..s11: never written *)
        repeat split;
          (rewrite /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1 /T4 /T3 /T2 /T1
                   /M9 /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1
                   /L9 /L8 /L7 /L6 /L5 /L4 /L3 /L2 /L1
                   /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1;
           repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
           reflexivity). }
      { exact (ptree_same_rep0_refl t). }
      { (* the level0 payload *)
        right. exists p2, p1, w.
        split; [exact (ptree_maps_level0 t vpn p2 p1 w Hmaps) |].
        assert (HE9a0 : E9 !!! Regidx (mword_of_int 10 : mword 5)
                        = u_pte_addr (pt_base c0) (vpn_idx 0 vpn)).
        { rewrite /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
          repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
          exact HT4a0. }
        rewrite HE9a0.
        unfold pt_addr0. rewrite Hch1. reflexivity. }
  Abort.

End Walk.
