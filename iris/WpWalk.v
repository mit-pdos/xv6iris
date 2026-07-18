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
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
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

  (* ================================================================= *)
  (* THE SHARED EPILOGUE (+0x52..+0x64): every exit path funnels here    *)
  (* with the loop-exit register file [Mf], the eight frame cells still  *)
  (* holding the entry values, and the result payload already decided.   *)
  (* Qed-sealed once so the four paths do not each re-pay its ~30        *)
  (* sentences (CLAUDE.md chunk-lemma rule).                             *)
  (* ================================================================= *)
  Lemma wp_walk_epilogue (R : s_regime) (Φ : mval -> iProp Σ)
      (γ : gname) (γc : gname) (bsie : mword 1)
      (mm Mf : gmap regidx (mword 64)) (t tf : ptree) (n : nat) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (22 <= n)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4) ->
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    ptree_same_rep0 t tf ->
    ((Mf !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0)
     \/ (exists p2 p1 w0, ptree_level0 tf vpn p2 p1 w0
          /\ Mf !!! Regidx (mword_of_int 10 : mword 5) = pt_addr0 p1 vpn)) ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
    sr_inv R -∗ kernel_text -∗
    pc_is (mword_of_int (WK + 0x52)) -∗
    gpr_file Mf -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    stack_own spr (n - 8) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
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
    intros va vpn sp0 spr ret_tgt Hn Hsp Htp Hx23 Hx24 Hx25 Hx26 Hx27 Hsame Hpay.
    iIntros "Hcfg Htoken Htlbinv #Htext Hpc Hfile
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hdeep Hptree Henv Hcont".
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
    (* +0x52 c.ldsp x1,56(sp) *)
    pose proof Hsp as HspMf.
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x52)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
              Mf (mm !!! Regidx (mword_of_int 1 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi52 [Hc56] [-]").
    { iEval (rewrite HspMf Hb1). iExact "Hc56". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc56".
    iEval (rewrite HspMf Hb1) in "Hc56".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> Mf).
    assert (Hpp52n : add_vec_int (mword_of_int (WK + 0x52) : mword 64) 2 = mword_of_int (WK + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52n) in "Hpc".
    (* +0x54 c.ldsp x8,48(sp) *)
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
    { rewrite /E1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspMf. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x54)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              E1 (mm !!! Regidx (mword_of_int 8 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi54 [Hc48] [-]").
    { iEval (rewrite HspE1 Hb2). iExact "Hc48". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc48".
    iEval (rewrite HspE1 Hb2) in "Hc48".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (Hpp54n : add_vec_int (mword_of_int (WK + 0x54) : mword 64) 2 = mword_of_int (WK + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54n) in "Hpc".
    (* +0x56 c.ldsp x9,40(sp) *)
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spr).
    { rewrite /E2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE1. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x56)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              E2 (mm !!! Regidx (mword_of_int 9 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi56 [Hc40] [-]").
    { iEval (rewrite HspE2 Hb3). iExact "Hc40". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc40".
    iEval (rewrite HspE2 Hb3) in "Hc40".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (Hpp56n : add_vec_int (mword_of_int (WK + 0x56) : mword 64) 2 = mword_of_int (WK + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56n) in "Hpc".
    (* +0x58 c.ldsp x18,32(sp) *)
    assert (HspE3 : E3 !!! Regidx csp_rs1 = spr).
    { rewrite /E3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE2. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x58)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              E3 (mm !!! Regidx (mword_of_int 18 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi58 [Hc32] [-]").
    { iEval (rewrite HspE3 Hb4). iExact "Hc32". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc32".
    iEval (rewrite HspE3 Hb4) in "Hc32".
    set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 18 : mword 5))]> E3).
    assert (Hpp58n : add_vec_int (mword_of_int (WK + 0x58) : mword 64) 2 = mword_of_int (WK + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58n) in "Hpc".
    (* +0x5a c.ldsp x19,24(sp) *)
    assert (HspE4 : E4 !!! Regidx csp_rs1 = spr).
    { rewrite /E4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE3. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x5a)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              E4 (mm !!! Regidx (mword_of_int 19 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi5a [Hc24] [-]").
    { iEval (rewrite HspE4 Hb5). iExact "Hc24". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc24".
    iEval (rewrite HspE4 Hb5) in "Hc24".
    set (E5 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 19 : mword 5))]> E4).
    assert (Hpp5an : add_vec_int (mword_of_int (WK + 0x5a) : mword 64) 2 = mword_of_int (WK + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5an) in "Hpc".
    (* +0x5c c.ldsp x20,16(sp) *)
    assert (HspE5 : E5 !!! Regidx csp_rs1 = spr).
    { rewrite /E5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE4. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x5c)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              E5 (mm !!! Regidx (mword_of_int 20 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi5c [Hc16] [-]").
    { iEval (rewrite HspE5 Hb6). iExact "Hc16". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc16".
    iEval (rewrite HspE5 Hb6) in "Hc16".
    set (E6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 20 : mword 5))]> E5).
    assert (Hpp5cn : add_vec_int (mword_of_int (WK + 0x5c) : mword 64) 2 = mword_of_int (WK + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5cn) in "Hpc".
    (* +0x5e c.ldsp x21,8(sp) *)
    assert (HspE6 : E6 !!! Regidx csp_rs1 = spr).
    { rewrite /E6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE5. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x5e)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              E6 (mm !!! Regidx (mword_of_int 21 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi5e [Hc08] [-]").
    { iEval (rewrite HspE6 Hb7). iExact "Hc08". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc08".
    iEval (rewrite HspE6 Hb7) in "Hc08".
    set (E7 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 21 : mword 5))]> E6).
    assert (Hpp5en : add_vec_int (mword_of_int (WK + 0x5e) : mword 64) 2 = mword_of_int (WK + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5en) in "Hpc".
    (* +0x60 c.ldsp x22,0(sp) *)
    assert (HspE7 : E7 !!! Regidx csp_rs1 = spr).
    { rewrite /E7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE6. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x60)) (mword_of_int 0 : mword 6) (mword_of_int 22 : mword 5)
              E7 (mm !!! Regidx (mword_of_int 22 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi60 [Hc00] [-]").
    { iEval (rewrite HspE7 Hb8). iExact "Hc00". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc00".
    iEval (rewrite HspE7 Hb8) in "Hc00".
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
    assert (HspE8 : E8 !!! Regidx csp_rs1 = spr).
    { rewrite /E8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspE7. }
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
      iSplitL "Hc56". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc56". }
      iSplitL "Hc48". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc48". }
      iSplitL "Hc40". { iExists (mm !!! Regidx (mword_of_int 9)). iExact "Hc40". }
      iSplitL "Hc32". { iExists (mm !!! Regidx (mword_of_int 18)). iExact "Hc32". }
      iSplitL "Hc24". { iExists (mm !!! Regidx (mword_of_int 19)). iExact "Hc24". }
      iSplitL "Hc16". { iExists (mm !!! Regidx (mword_of_int 20)). iExact "Hc16". }
      iSplitL "Hc08". { iExists (mm !!! Regidx (mword_of_int 21)). iExact "Hc08". }
      iSplitL "Hc00". { iExists (mm !!! Regidx (mword_of_int 22)). iExact "Hc00". }
      done. }
    iEval (rewrite -Hsprstk) in "Hdeep".
    iDestruct (stack_own_split_2 sp0 8 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
    iApply ("Hcont" $! E9 tf with "Hcfg Htoken Htlbinv Hpc Hfile Hstk Hptree Henv [%] [%] [%]").
    { (* callee_saved mm E9 *)
      unfold callee_saved.
      split.
      { rewrite /E9 lookup_total_insert. rewrite HspE8.
        unfold spr. apply walk_sp_cancel. }
      split.
      { (* tp *)
        rewrite /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        exact Htp. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E8 /E7 /E6 /E5 /E4 /E3.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E8 /E7 /E6 /E5 /E4.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E8 /E7 /E6 /E5.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E8 /E7 /E6.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E8 /E7.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E8.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E8 lookup_total_insert. reflexivity. }
      (* s7..s11 *)
      repeat split;
        (rewrite /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1;
         repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
         first [ exact Hx23 | exact Hx24 | exact Hx25 | exact Hx26 | exact Hx27 ]). }
    { exact Hsame. }
    { (* the payload: a0 is untouched by the epilogue *)
      assert (HE9a0 : E9 !!! Regidx (mword_of_int 10 : mword 5)
                      = Mf !!! Regidx (mword_of_int 10 : mword 5)).
      { rewrite /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
        reflexivity. }
      rewrite HE9a0. exact Hpay. }
  Qed.

  (* ================================================================= *)
  (* THE SHARED TAIL (+0x46..+0x50): a0 := &level-0 slot, then the       *)
  (* epilogue.  All four success paths funnel here with s1 = the L0      *)
  (* node's page base [b0] and the level0 path fact.                     *)
  (* ================================================================= *)
  Lemma wp_walk_tail (R : s_regime) (Φ : mval -> iProp Σ)
      (γ : gname) (γc : gname) (bsie : mword 1)
      (mm Mf : gmap regidx (mword 64)) (t tf : ptree) (b0 : mword 44) (n : nat) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (22 <= n)%nat ->
    uint va < 274877906944 ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 19 : mword 5) = va ->
    Mf !!! Regidx (mword_of_int 9 : mword 5)
      = zero_extend' 64 (concat_vec b0 (zeros' 12 : mword 12)) ->
    Mf !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4) ->
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    ptree_same_rep0 t tf ->
    (exists p2 p1 w0, ptree_level0 tf vpn p2 p1 w0
       /\ pt_addr0 p1 vpn = u_pte_addr b0 (vpn_idx 0 vpn)) ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
    sr_inv R -∗ kernel_text -∗
    pc_is (mword_of_int (WK + 0x46)) -∗
    gpr_file Mf -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    stack_own spr (n - 8) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
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
    intros va vpn sp0 spr ret_tgt Hn Hva' Hsp Hs3 Hs1 Htp Hx23 Hx24 Hx25 Hx26 Hx27 Hsame Hlvl.
    iIntros "Hcfg Htoken Htlbinv #Htext Hpc Hfile
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hdeep Hptree Henv Hcont".
    iPoseProof (wi_46 with "Htext") as "Hi46".
    iPoseProof (wi_4a with "Htext") as "Hi4a".
    iPoseProof (wi_4e with "Htext") as "Hi4e".
    iPoseProof (wi_50 with "Htext") as "Hi50".
    (* +0x46 srli a0,s3,12 *)
    iApply (wp_srli4_s_scfg_r R γc Φ (mword_of_int (WK + 0x46)) (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 12 : mword 6)
              Mf (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi46 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (T1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (shift_bits_right (Mf !!! Regidx (mword_of_int 19 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> Mf).
    assert (Hpp4a : add_vec_int (mword_of_int (WK + 0x46) : mword 64) 4 = mword_of_int (WK + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* +0x4a andi a0,a0,511 *)
    iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x4a)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 511 : mword 12)
              (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                       (sign_extend' 64 (mword_of_int 511 : mword 12)))
              T1 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /T1 lookup_total_insert; rewrite Hs3; reflexivity)
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
                    = zero_extend' 64 (concat_vec b0 (zeros' 12 : mword 12))).
    { rewrite /T3 /T2 /T1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      exact Hs1. }
    assert (HT4a0 : T4 !!! Regidx (mword_of_int 10 : mword 5)
                    = u_pte_addr b0 (vpn_idx 0 vpn)).
    { rewrite /T4 lookup_total_insert.
      rewrite {1}/T3 lookup_total_insert.
      rewrite HT3s1.
      replace (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
        with (subrange_vec_dec (mword_of_int 12 : mword 64) (Z.sub log2_xlen 1) 0)
        by (apply bv_eq; vm_compute; reflexivity).
      exact (walk_slot_addr0 b0 va Hva'). }
    (* funnel into the shared epilogue *)
    iApply (wp_walk_epilogue R Φ γ γc bsie mm T4 t tf n Hn
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hsp)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Htp)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hx23)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hx24)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hx25)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hx26)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    exact Hx27)
              Hsame
              ltac:(destruct Hlvl as (p2 & p1 & w0 & Hl0 & Heq);
                    right; exists p2, p1, w0; split;
                    [exact Hl0 | rewrite HT4a0 Heq; reflexivity])
              with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                    Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                    Hdeep Hptree Henv Hcont").
  Qed.

  (* ================================================================= *)
  (* THE SHARED ALLOCATION ARM (+0x72..+0x94): kalloc, memset(0), the    *)
  (* pointer-PTE store through the caller's GRAFT interface, and the     *)
  (* c.j rejoin -- or kalloc's null exit straight through the epilogue.  *)
  (* Used by arm 1 (twice: graft2 then graft1) and arm 2 (graft1).       *)
  (* ================================================================= *)
  Lemma wp_walk_alloc (R : s_regime) (Φ : mval -> iProp Σ)
      (γ : gname) (γc : gname) (bsie : mword 1)
      (mm Mf : gmap regidx (mword 64)) (t tf : ptree)
      (tG : mword 44 -> ptree) (clvl : nat)
      (cellA : mword 64) (w0 : bv 64) (n : nat) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (22 <= n)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 18 : mword 5) = cellA ->
    eq_vec (Mf !!! Regidx (mword_of_int 22 : mword 5)) zero_reg = false ->
    Mf !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4) ->
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    ptree_same_rep0 t tf ->
    (ptree_own 2 (DfracOwn 1) tf ⊢
       cellA ↦₈ w0 ∗
       (∀ b : mword 44,
          cellA ↦₈ pt_ptr_pte b -∗
          ptree_own clvl (DfracOwn 1) (pt_empty_node b) -∗
          ptree_own 2 (DfracOwn 1) (tG b))) ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
    sr_inv R -∗ kernel_text -∗
    pc_is (mword_of_int (WK + 0x72)) -∗
    gpr_file Mf -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    stack_own spr (n - 8) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
    ( ∀ (Mo : gmap regidx (mword 64)) (b : mword 44),
      ⌜forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
         Mo !!! Regidx c = Mf !!! Regidx c⌝ -∗
      ⌜Mo !!! Regidx (mword_of_int 9 : mword 5)
         = zero_extend' 64 (concat_vec b (zeros' 12 : mword 12))⌝ -∗
      smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
      sr_inv R -∗
      pc_is (mword_of_int (WK + 0x40)) -∗
      gpr_file Mo -∗
      pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
      pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
      pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
      pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
      pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
      pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
      pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
      pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
      stack_own spr (n - 8) -∗
      ptree_own 2 (DfracOwn 1) (tG b) -∗
      kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
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
        \/ (exists p2 p1 w1,
             ptree_level0 t' vpn p2 p1 w1 /\
             mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va vpn sp0 spr ret_tgt Hn Hsp Hs2c Hs6 Htp Hx23 Hx24 Hx25 Hx26 Hx27 Hsame Hacc.
    iIntros "Hcfg Htoken Htlbinv #Htext Hpc Hfile
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hdeep Hptree Henv Hok Hcont".
    iPoseProof (wi_72 with "Htext") as "Hi72".
    iPoseProof (wi_76 with "Htext") as "Hi76".
    iPoseProof (wi_7a with "Htext") as "Hi7a".
    iPoseProof (wi_7c with "Htext") as "Hi7c".
    (* +0x72 beqz s6 FALLS (alloc = 1) *)
    iApply (wp_beqz_x0_fall_s_scfg_r R γc Φ (mword_of_int (WK + 0x72)) (mword_of_int 36 : mword 13) (mword_of_int 22 : mword 5)
              Mf (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate) Hs6
              with "Hcfg Htlbinv Hpc Hfile Hi72 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp76 : add_vec_int (mword_of_int (WK + 0x72) : mword 64) 4 = mword_of_int (WK + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp76) in "Hpc".
    (* +0x76 jal kalloc *)
    iApply (wp_jal_gpr_s_zca_r R γc Φ (mword_of_int (WK + 0x76)) (mword_of_int 1 : mword 5) (mword_of_int 2095964 : mword 21)
              Mf 1%Qp
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi76 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (J := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (WK + 0x76) : mword 64) 4)]> Mf).
    assert (Htgtk : add_vec (mword_of_int (WK + 0x76) : mword 64) (sign_extend' 64 (mword_of_int 2095964 : mword 21)) = mword_of_int KernelSyms.kalloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtk) in "Hpc".
    (* ---- kalloc() through the env bundle ---- *)
    iDestruct "Henv" as (qint qcpu) "(%Hqne & %H0ne & #Hlock & Hnoff & Hint & Hqcpu)".
    assert (HspJ : J !!! Regidx csp_rs1 = spr).
    { rewrite /J. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hsp. }
    iApply (wp_kalloc_r R Φ γ J qcpu (zeros' 32) qint
              (mycpu_ret (mm !!! Regidx (mword_of_int 4)))
              (mword_of_int (KernelSyms.kmem + 24)) γc bsie (n - 8)%nat
              ltac:(lia)
              ltac:(repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    rewrite Htp; exact Hqne)
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              ltac:(reflexivity)
              ltac:(repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    rewrite Htp; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(replace (eq_vec (sign_extend' 64 (zeros' 32 : mword 32)) zero_reg) with true
                      by (vm_compute; reflexivity);
                    vm_compute; reflexivity)
              with "Hcfg Htoken Htlbinv Htext Hpc Hfile [Hdeep] [Hnoff] [Hint] [Hlock] [Hqcpu] [-]").
    { iEval (rewrite HspJ). iExact "Hdeep". }
    { iExact "Hnoff". }
    { iExact "Hint". }
    { match goal with |- environments.envs_entails _ (is_lock _ ?a _) =>
        replace a with (mword_of_int KernelSyms.kmem : mword 64) end.
      2:{ rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert.
          rewrite lookup_total_insert.
          apply bv_eq; vm_compute; reflexivity. }
      iExact "Hlock". }
    { match goal with |- environments.envs_entails _ (word_pointsto (add_vec ?a _) _ _) =>
        replace a with (mword_of_int KernelSyms.kmem : mword 64) end.
      2:{ rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite lookup_total_insert.
          rewrite lookup_total_insert.
          apply bv_eq; vm_compute; reflexivity. }
      iExact "Hqcpu". }
    iIntros (mr) "Hcfg Htoken Htlbinv Hpc Hfile %Hkcs Hkpost Hstk Hqcpu Hnoff Hint".
    (* normalize the returned lock-cpu cell's address to the concrete kmem *)
    iEval (rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
           rewrite lookup_total_insert;
           rewrite lookup_total_insert;
           rewrite /regval_into_reg) in "Hqcpu".
    assert (Hqaddr : add_vec (add_vec (add_vec (mword_of_int (KernelSyms.kalloc + 10) : mword 64)
                        (auipc_off (mword_of_int 17 : mword 20)))
                        (sign_extend' 64 (mword_of_int 0x7f0 : mword 12)))
                        (sign_extend' 64 (mword_of_int 16 : mword 12))
                     = add_vec (mword_of_int KernelSyms.kmem : mword 64)
                        (sign_extend' 64 (mword_of_int 16 : mword 12)))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hqaddr) in "Hqcpu".
    (* the return pc: +0x7a *)
    match goal with |- context [pc_is ?tgt] => idtac end.
    assert (Hret7a : update_vec_dec (add_vec (J !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0" : mword 1) = mword_of_int (WK + 0x7a)).
    { rewrite /J lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret7a) in "Hpc".
    (* +0x7a c.mv s1,a0 *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x7a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mr (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi7a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (N1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mr !!! Regidx (mword_of_int 10 : mword 5)))]> mr).
    assert (Hpp7c : add_vec_int (mword_of_int (WK + 0x7a) : mword 64) 2 = mword_of_int (WK + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7c) in "Hpc".
    (* the kalloc-env repack (both branches restore the quiescent state) *)
    assert (Hqnr : (autocast (T := mword) (subrange_vec_dec
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (sign_extend' 64 ((autocast (T := mword) (subrange_vec_dec
              (sign_extend' 64 (subrange_vec_dec
                 (add_vec (sign_extend' 64 (zeros' 32 : mword 32))
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
              (Z.sub (Z.mul 4 8) 0x1) 0) : mword 32)))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
        (Z.sub (Z.mul 4 8) 0x1) 0) : mword 32) = (zeros' 32 : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    iAssert (kalloc_env γ (mm !!! Regidx (mword_of_int 4)))
      with "[Hqcpu Hnoff Hint]" as "Henv".
    { iExists (if eq_vec (sign_extend' 64 (zeros' 32 : mword 32)) zero_reg
               then (zeros' 32 : mword 32) else qint), (zero_reg : mword 64).
      iSplitR. { iPureIntro. exact H0ne. }
      iSplitR. { iPureIntro. exact H0ne. }
      iFrame "Hlock".
      iSplitL "Hnoff".
      { iEval (rewrite Hqnr) in "Hnoff". iExact "Hnoff". }
      iSplitL "Hint". { iExact "Hint". }
      iExact "Hqcpu". }
    (* +0x7c c.beqz a0: the null/success split *)
    iDestruct "Hkpost" as "[%Hnull | [%Hpv Hpage]]".
    { (* ---- NULL: exit through the epilogue with a0 = 0 ---- *)
      assert (HN1a0 : N1 !!! Regidx (mword_of_int 10 : mword 5) = mr !!! Regidx (mword_of_int 10 : mword 5)).
      { rewrite /N1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iApply (wp_cbeqz_taken_s_zca_scfg_r R γc Φ (mword_of_int (WK + 0x7c)) (mword_of_int 235 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
                N1 (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HN1a0 Hnull; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi7c [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Htgt52 : add_vec (mword_of_int (WK + 0x7c) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 235 : mword 8) ('b"0"))))
              = mword_of_int (WK + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt52) in "Hpc".
      iEval (rewrite HspJ) in "Hstk".
      iApply (wp_walk_epilogue R Φ γ γc bsie mm N1 t tf n Hn
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                      rewrite (callee_saved_lookup Hkcs (csp_rs1 : mword 5)
                                 ltac:(vm_compute; reflexivity));
                      exact HspJ)
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 4)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                      exact Htp)
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 23)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                      exact Hx23)
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 24)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                      exact Hx24)
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 25)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                      exact Hx25)
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 26)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                      exact Hx26)
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 27)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                      exact Hx27)
                Hsame
                ltac:(left; rewrite HN1a0 Hnull; reflexivity)
                with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hstk Hptree Henv Hcont"). }
    (* ---- SUCCESS: page p, memset(0), graft, store, rejoin ---- *)
    iPoseProof (wi_7e with "Htext") as "Hi7e".
    iPoseProof (wi_80 with "Htext") as "Hi80".
    iPoseProof (wi_82 with "Htext") as "Hi82".
    iPoseProof (wi_86 with "Htext") as "Hi86".
    iPoseProof (wi_8a with "Htext") as "Hi8a".
    iPoseProof (wi_8c with "Htext") as "Hi8c".
    iPoseProof (wi_90 with "Htext") as "Hi90".
    iPoseProof (wi_94 with "Htext") as "Hi94".
    assert (HN1a0 : N1 !!! Regidx (mword_of_int 10 : mword 5) = mr !!! Regidx (mword_of_int 10 : mword 5)).
    { rewrite /N1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hnz : (zero_reg : mword 64) = nullp) by (apply bv_eq; vm_compute; reflexivity).
    (* the allocated page's bounds and its ppn *)
    pose proof Hpv as Hpv'.
    destruct Hpv' as [Hal Hrange]. unfold page_in_range, kmem_lo, kmem_hi in Hrange.
    unfold page_aligned, PGSIZE in Hal.
    assert (Hlt56 : uint (mr !!! Regidx (mword_of_int 10 : mword 5)) < 72057594037927936) by lia.
    set (bppn := (autocast (T := mword) (subrange_vec_dec (mr !!! Regidx (mword_of_int 10 : mword 5)) 55 12) : mword 44)).
    assert (Hpb : zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))
                  = mr !!! Regidx (mword_of_int 10 : mword 5))
      by (exact (walk_alloc_page_base _ Hal Hlt56)).
    (* +0x7c c.beqz a0 FALLS (p <> 0) *)
    iApply (wp_cbeqz_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x7c)) (mword_of_int 235 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              N1 (dq:=DfracOwn 1)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite HN1a0; apply eq_vec_false_iff; rewrite Hnz;
                    exact (page_valid_ne_null _ Hpv))
              with "Hcfg Htlbinv Hpc Hfile Hi7c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp7e : add_vec_int (mword_of_int (WK + 0x7c) : mword 64) 2 = mword_of_int (WK + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7e) in "Hpc".
    (* +0x7e c.lui a2,1 *)
    iApply (wp_clui_s_r R γc Φ (mword_of_int (WK + 0x7e)) (mword_of_int 12 : mword 5)
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              N1 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi7e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (N2 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 4096 : mword 64)]> N1).
    assert (Hpp80 : add_vec_int (mword_of_int (WK + 0x7e) : mword 64) 2 = mword_of_int (WK + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp80) in "Hpc".
    (* +0x80 c.li a1,0 *)
    iApply (wp_cli_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x80)) (mword_of_int 11 : mword 5) (mword_of_int 0 : mword 6)
              N2 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi80 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (N3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> N2).
    assert (Hpp82 : add_vec_int (mword_of_int (WK + 0x80) : mword 64) 2 = mword_of_int (WK + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp82) in "Hpc".
    (* +0x82 jal memset *)
    iApply (wp_jal_gpr_s_zca_r R γc Φ (mword_of_int (WK + 0x82)) (mword_of_int 1 : mword 5) (mword_of_int 2096362 : mword 21)
              N3 1%Qp
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi82 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (N4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (WK + 0x82) : mword 64) 4)]> N3).
    assert (Htgtm : add_vec (mword_of_int (WK + 0x82) : mword 64) (sign_extend' 64 (mword_of_int 2096362 : mword 21)) = mword_of_int KernelSyms.memset)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtm) in "Hpc".
    (* memset(p, 0, 4096) keeping the zero bytes *)
    assert (HN4a0 : N4 !!! Regidx (mword_of_int 10 : mword 5) = mr !!! Regidx (mword_of_int 10 : mword 5)).
    { rewrite /N4 /N3 /N2 /N1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      reflexivity. }
    iApply (wp_memset_page_zero_r R Φ N4 (mword_of_int 0 : mword 64) (n - 8)%nat γc (dq:=DfracOwn 1)
              ltac:(lia)
              ltac:(rewrite HN4a0; exact Hpv)
              ltac:(rewrite /N4; rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                    rewrite /N3 lookup_total_insert; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /N4 /N3;
                    repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
                    rewrite lookup_total_insert; reflexivity)
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              with "Hcfg Htlbinv Htext Hpc Hfile [Hstk] [Hpage] [-]").
    { iEval (rewrite HspJ) in "Hstk".
      match goal with |- environments.envs_entails _ (stack_own ?a _) =>
        replace a with spr end.
      2:{ symmetry. rewrite /N4 /N3 /N2 /N1.
          repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
          rewrite (callee_saved_lookup Hkcs (csp_rs1 : mword 5)
                     ltac:(vm_compute; reflexivity)).
          exact HspJ. }
      iExact "Hstk". }
    { iEval (rewrite HN4a0). iExact "Hpage". }
    iIntros (mfin) "Hcfg Htlbinv Hpc Hstk Hbytes Hfile %Hmcs".
    assert (Hret86 : update_vec_dec (add_vec (N4 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0" : mword 1) = mword_of_int (WK + 0x86)).
    { rewrite /N4 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret86) in "Hpc".
    (* the zero page as a description node *)
    assert (Hcb : nth_byte (autocast (T := mword) (subrange_vec_dec (mword_of_int 0 : mword 64) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 = (mword_of_int 0 : mword 8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hcb HN4a0 -Hpb) in "Hbytes".
    iDestruct (zero_page_to_node clvl (DfracOwn 1) bppn with "Hbytes") as "Hchild".
    (* +0x86 srli a5,s1,12 *)
    assert (Hmfs1 : mfin !!! Regidx (mword_of_int 9 : mword 5)
                    = add_vec zero_reg (mr !!! Regidx (mword_of_int 10 : mword 5))).
    { rewrite (callee_saved_lookup Hmcs (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /N4 /N3 /N2.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite /N1 lookup_total_insert. reflexivity. }
    iApply (wp_srli4_s_scfg_r R γc Φ (mword_of_int (WK + 0x86)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
              mfin (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi86 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (P1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (mfin !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> mfin).
    assert (Hpp8a : add_vec_int (mword_of_int (WK + 0x86) : mword 64) 4 = mword_of_int (WK + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8a) in "Hpc".
    (* +0x8a c.slli a5,10 *)
    iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x8a)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 6)
              (shift_bits_left (P1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
              P1 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi8a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (P2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (P1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> P1).
    assert (Hpp8c : add_vec_int (mword_of_int (WK + 0x8a) : mword 64) 2 = mword_of_int (WK + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8c) in "Hpc".
    (* +0x8c ori a5,a5,1 *)
    iApply (wp_ori_s_r R γc Φ (mword_of_int (WK + 0x8c)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 12)
              (or_vec (P2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
              P2 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi8c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (P3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (or_vec (P2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> P2).
    assert (Hpp90 : add_vec_int (mword_of_int (WK + 0x8c) : mword 64) 4 = mword_of_int (WK + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp90) in "Hpc".
    assert (HP3a5 : P3 !!! Regidx (mword_of_int 15 : mword 5) = pt_ptr_pte bppn).
    { rewrite /P3 lookup_total_insert.
      rewrite {1}/P2 lookup_total_insert.
      rewrite {1}/P1 lookup_total_insert.
      rewrite Hmfs1 add_vec_zero_l.
      exact (walk_alloc_pte _ Hal Hlt56). }
    (* +0x90 sd a5,0(s2): the pointer-PTE store through the graft cell *)
    assert (HP3s2 : P3 !!! Regidx (mword_of_int 18 : mword 5) = cellA).
    { rewrite /P3 /P2 /P1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite (callee_saved_lookup Hmcs (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite /N4 /N3 /N2 /N1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite (callee_saved_lookup Hkcs (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite /J. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs2c. }
    assert (Hea0' : forall X : mword 64, add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iDestruct (Hacc with "Hptree") as "[Hcell Hgw]".
    iApply (wp_sd_s_scfg_r R γc Φ (mword_of_int (WK + 0x90)) (mword_of_int 15 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
              P3 w0 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi90 [Hcell] [-]").
    { iEval (rewrite Hea0' HP3s2). iExact "Hcell". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hcell".
    iEval (rewrite Hea0' HP3s2 HP3a5) in "Hcell".
    iDestruct ("Hgw" $! bppn with "Hcell Hchild") as "Hptree".
    assert (Hpp94 : add_vec_int (mword_of_int (WK + 0x90) : mword 64) 4 = mword_of_int (WK + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp94) in "Hpc".
    (* +0x94 c.j back to the loop decrement at +0x40 *)
    iApply (wp_cj_s_scfg_r R γc Φ (mword_of_int (WK + 0x94))
              (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0")))
              P3 (dq:=DfracOwn 1)
              ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi94 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Htgt40 : add_vec (mword_of_int (WK + 0x94) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0"))))
            = mword_of_int (WK + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt40) in "Hpc".
    (* hand off to the success continuation *)
    iApply ("Hok" $! P3 bppn with "[%] [%] Hcfg Htoken Htlbinv Hpc Hfile
            Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 [Hstk] Hptree Henv").
    { (* the callee-saved-except-s1 transport back to Mf *)
      intros c Hcs Hc9.
      rewrite /P3 /P2 /P1.
      repeat (rewrite lookup_total_insert_ne;
        [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hcs; discriminate]).
      rewrite (callee_saved_lookup Hmcs c Hcs).
      rewrite /N4 /N3 /N2.
      repeat (rewrite lookup_total_insert_ne;
        [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hcs; discriminate]).
      rewrite /N1.
      rewrite lookup_total_insert_ne;
        [| intros Habs; injection Habs as Habs2; exact (Hc9 (eq_sym Habs2))].
      rewrite (callee_saved_lookup Hkcs c Hcs).
      rewrite /J.
      rewrite lookup_total_insert_ne;
        [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hcs; discriminate].
      reflexivity. }
    { (* s1 = the new page's base *)
      rewrite /P3 /P2 /P1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite Hmfs1 add_vec_zero_l.
      symmetry. exact Hpb. }
    { (* the deep stack, back at spr *)
      match goal with |- environments.envs_entails _ (stack_own ?a _) => idtac end.
      iEval (rewrite /N4 /N3 /N2 /N1;
             repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]);
             rewrite (callee_saved_lookup Hkcs (csp_rs1 : mword 5)
                        ltac:(vm_compute; reflexivity));
             rewrite HspJ) in "Hstk".
      iExact "Hstk". }
  Qed.


  (* wp_walk_r's script (paths 1 and arm-3 proven, funneling through the
     sealed chunks) is STASHED in WpWalk_body.stash while wp_walk_alloc
     is developed -- re-splice it after this lemma reaches Qed. *)


End Walk.
