(* WpSconfWalk.v -- the whole-function WP for xv6's walk() over the
   SIE-agnostic sconf world (the sconf mirror of WpWalk.v's wp_walk_r). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv.
Require Import WpLock.
Require Import VcGen.
Require Import CommonWalk PtTree KptTree.
Require Import PtBuild KvmSpec.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpMemsetS WpMemsetInstr.
Require Import SpecMemset.
Require Import SpecKalloc.
Require Import WpWalkInstr UserBits.
Require Import WpMemsetPage.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import RiscvExec RiscvTryStep.
Require Import SpecWalk.
Import Defs.
Local Open Scope Z_scope.


Module WalkProof (Kalloc : KALLOC) (Memset : MEMSET) : WALK.

Section WpSconfWalk.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  Notation WK := KernelSyms.walk.

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* peel_reg peels via the upd_ne/upd_eq LEMMAS (values stay opaque), so it is
     safe even where the target is a symbolic HIT (e.g. [M9 !!! csp = spr] with
     [spr = add_vec sp0 …]) — a bare [reg_lookup]/vm_compute would try to reduce
     that add_vec and hang.  Over the transparent-but-compact [rf_upd] spine these
     lemma-rewrites are already ~2.5x faster than the old gmap peel. *)
  Ltac peel_reg :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ];
    reflexivity.

  (* the +64/-64 c.addi16sp frame cancel *)
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
  (* THE SHARED EPILOGUE (+0x52..+0x64) -- sconf mirror.                 *)
  (* ================================================================= *)
  Lemma wp_walk_epilogue_sconf (γ : gname) (root_ppn : mword 44) (γa : gname) (Φ : mval -> iProp Σ)
      (mm Mf : regfile) (t tf : ptree) (K : nat) (lvl : nat) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (22 <= K)%nat ->
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
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn Mf (K - 8)%nat -∗ intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
    kernel_text -∗
    pc_is (mword_of_int (WK + 0x52)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γa (mm !!! Regidx (mword_of_int 4)) -∗
    ( ∀ (mr : regfile) (t' : ptree),
      sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap_gpr γ root_ppn mr K -∗ intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γa (mm !!! Regidx (mword_of_int 4)) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ptree_same_rep0 t t'⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
        \/ (exists p2 p1 w0,
             ptree_level0 t' vpn p2 p1 w0 /\
             mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va vpn sp0 spr ret_tgt HK Hsp Htp Hx23 Hx24 Hx25 Hx26 Hx27 Hsame Hpay.
    iIntros "Hsc Hhs Hcg Hcnt Htlbinv #Htext Hpc
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hptree Henv Hcont".
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
    assert (Hdeepaddr : pa_stk (pa_stk sp0 kv_frame_slots) 8 = pa_stk spr kv_frame_slots).
    { unfold spr, sp0, pa_stk, add_vec_int, kv_frame_slots. rewrite !add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
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
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x52)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
              Mf (K - 8)%nat (mm !!! Regidx (mword_of_int 1 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi52 [Hc56] [-]").
    { iEval (rewrite HspMf Hb1). iExact "Hc56". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc56".
    iEval (rewrite HspMf Hb1) in "Hc56".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> Mf).
    assert (Hpp52n : add_vec_int (mword_of_int (WK + 0x52) : mword 64) 2 = mword_of_int (WK + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52n) in "Hpc".
    (* +0x54 c.ldsp x8,48(sp) *)
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
    { rewrite /E1. rewrite upd_ne; [| reg_neq]. exact HspMf. }
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x54)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 8)%nat (mm !!! Regidx (mword_of_int 8 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi54 [Hc48] [-]").
    { iEval (rewrite HspE1 Hb2). iExact "Hc48". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc48".
    iEval (rewrite HspE1 Hb2) in "Hc48".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (Hpp54n : add_vec_int (mword_of_int (WK + 0x54) : mword 64) 2 = mword_of_int (WK + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54n) in "Hpc".
    (* +0x56 c.ldsp x9,40(sp) *)
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spr).
    { rewrite /E2. rewrite upd_ne; [| reg_neq]. exact HspE1. }
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x56)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 8)%nat (mm !!! Regidx (mword_of_int 9 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi56 [Hc40] [-]").
    { iEval (rewrite HspE2 Hb3). iExact "Hc40". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc40".
    iEval (rewrite HspE2 Hb3) in "Hc40".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (Hpp56n : add_vec_int (mword_of_int (WK + 0x56) : mword 64) 2 = mword_of_int (WK + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56n) in "Hpc".
    (* +0x58 c.ldsp x18,32(sp) *)
    assert (HspE3 : E3 !!! Regidx csp_rs1 = spr).
    { rewrite /E3. rewrite upd_ne; [| reg_neq]. exact HspE2. }
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x58)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              E3 (K - 8)%nat (mm !!! Regidx (mword_of_int 18 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi58 [Hc32] [-]").
    { iEval (rewrite HspE3 Hb4). iExact "Hc32". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc32".
    iEval (rewrite HspE3 Hb4) in "Hc32".
    set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 18 : mword 5))]> E3).
    assert (Hpp58n : add_vec_int (mword_of_int (WK + 0x58) : mword 64) 2 = mword_of_int (WK + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58n) in "Hpc".
    (* +0x5a c.ldsp x19,24(sp) *)
    assert (HspE4 : E4 !!! Regidx csp_rs1 = spr).
    { rewrite /E4. rewrite upd_ne; [| reg_neq]. exact HspE3. }
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x5a)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              E4 (K - 8)%nat (mm !!! Regidx (mword_of_int 19 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi5a [Hc24] [-]").
    { iEval (rewrite HspE4 Hb5). iExact "Hc24". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc24".
    iEval (rewrite HspE4 Hb5) in "Hc24".
    set (E5 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 19 : mword 5))]> E4).
    assert (Hpp5an : add_vec_int (mword_of_int (WK + 0x5a) : mword 64) 2 = mword_of_int (WK + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5an) in "Hpc".
    (* +0x5c c.ldsp x20,16(sp) *)
    assert (HspE5 : E5 !!! Regidx csp_rs1 = spr).
    { rewrite /E5. rewrite upd_ne; [| reg_neq]. exact HspE4. }
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x5c)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              E5 (K - 8)%nat (mm !!! Regidx (mword_of_int 20 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi5c [Hc16] [-]").
    { iEval (rewrite HspE5 Hb6). iExact "Hc16". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc16".
    iEval (rewrite HspE5 Hb6) in "Hc16".
    set (E6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 20 : mword 5))]> E5).
    assert (Hpp5cn : add_vec_int (mword_of_int (WK + 0x5c) : mword 64) 2 = mword_of_int (WK + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5cn) in "Hpc".
    (* +0x5e c.ldsp x21,8(sp) *)
    assert (HspE6 : E6 !!! Regidx csp_rs1 = spr).
    { rewrite /E6. rewrite upd_ne; [| reg_neq]. exact HspE5. }
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x5e)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              E6 (K - 8)%nat (mm !!! Regidx (mword_of_int 21 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi5e [Hc08] [-]").
    { iEval (rewrite HspE6 Hb7). iExact "Hc08". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc08".
    iEval (rewrite HspE6 Hb7) in "Hc08".
    set (E7 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 21 : mword 5))]> E6).
    assert (Hpp5en : add_vec_int (mword_of_int (WK + 0x5e) : mword 64) 2 = mword_of_int (WK + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5en) in "Hpc".
    (* +0x60 c.ldsp x22,0(sp) *)
    assert (HspE7 : E7 !!! Regidx csp_rs1 = spr).
    { rewrite /E7. rewrite upd_ne; [| reg_neq]. exact HspE6. }
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x60)) (mword_of_int 0 : mword 6) (mword_of_int 22 : mword 5)
              E7 (K - 8)%nat (mm !!! Regidx (mword_of_int 22 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi60 [Hc00] [-]").
    { iEval (rewrite HspE7 Hb8). iExact "Hc00". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc00".
    iEval (rewrite HspE7 Hb8) in "Hc00".
    set (E8 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 22 : mword 5))]> E7).
    assert (Hpp60n : add_vec_int (mword_of_int (WK + 0x60) : mword 64) 2 = mword_of_int (WK + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60n) in "Hpc".
    assert (HspE8 : E8 !!! Regidx csp_rs1 = spr).
    { rewrite /E8. rewrite upd_ne; [| reg_neq]. exact HspE7. }
    (* +0x62 c.addi16sp sp,+64 -- the frame pop (feed 8 slots back into avail) *)
    set (E9 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E8).
    assert (HspE9 : E9 !!! Regidx csp_rs1 = sp0).
    { rewrite /E9 upd_eq. rewrite HspE8. unfold spr. apply walk_sp_cancel. }
    assert (Hwv : add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0).
    { rewrite HspE8. unfold spr. apply walk_sp_cancel. }
    assert (Hpop : E8 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8).
    { rewrite Hwv HspE8. symmetry. exact Hsprstk. }
    iAssert (stack_own sp0 8) with "[Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hc56". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc56". }
      iSplitL "Hc48". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc48". }
      iSplitL "Hc40". { iExists (mm !!! Regidx (mword_of_int 9)). iExact "Hc40". }
      iSplitL "Hc32". { iExists (mm !!! Regidx (mword_of_int 18)). iExact "Hc32". }
      iSplitL "Hc24". { iExists (mm !!! Regidx (mword_of_int 19)). iExact "Hc24". }
      iSplitL "Hc16". { iExists (mm !!! Regidx (mword_of_int 20)). iExact "Hc16". }
      iSplitL "Hc08". { iExists (mm !!! Regidx (mword_of_int 21)). iExact "Hc08". }
      iSplitL "Hc00". { iExists (mm !!! Regidx (mword_of_int 22)). iExact "Hc00". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x62)) (mword_of_int 4 : mword 6)
              E8 (K - 8)%nat 8 Hpop
              with "Hsc Hhs Hcg Htlbinv Hpc Hi62 Hframe [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E8) with E9.
    assert (Hnk : ((K - 8) + 8)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp64 : add_vec_int (mword_of_int (WK + 0x62) : mword 64) 2 = mword_of_int (WK + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    (* +0x64 ret *)
    assert (HE9ra : E9 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { peel_reg. }
    assert (Hrt : update_vec_dec (add_vec (E9 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0" : mword 1) = ret_tgt).
    { rewrite HE9ra.
      replace (sign_extend' 64 (zeros' 12) : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. reflexivity. }
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x64)) (mword_of_int 1 : mword 5) E9 K
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hrt; exact (bit0_update0_64 (mm !!! Regidx (mword_of_int 1))))
              with "Hsc Hhs Hcg Htlbinv Hpc Hi64 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (rewrite Hrt) in "Hpc".
    iApply ("Hcont" $! E9 tf with "Hsc Hhs Hcg Hcnt Htlbinv Hpc Hptree Henv [%] [%] [%]").
    { (* callee_saved mm E9 *)
      unfold callee_saved.
      split.
      { rewrite /E9 upd_eq. rewrite HspE8. unfold spr. apply walk_sp_cancel. }
      split.
      { rewrite /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Htp. }
      split.
      { rewrite /E9. rewrite upd_ne; [| reg_neq]. peel_reg. }
      split.
      { rewrite /E9. rewrite upd_ne; [| reg_neq]. peel_reg. }
      split.
      { rewrite /E9. rewrite upd_ne; [| reg_neq]. peel_reg. }
      split.
      { rewrite /E9. rewrite upd_ne; [| reg_neq]. peel_reg. }
      split.
      { rewrite /E9. rewrite upd_ne; [| reg_neq]. peel_reg. }
      split.
      { rewrite /E9. rewrite upd_ne; [| reg_neq].
        rewrite /E8. repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq. reflexivity. }
      split.
      { rewrite /E9. rewrite upd_ne; [| reg_neq].
        rewrite /E8 upd_eq. reflexivity. }
      repeat split;
        (rewrite /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1;
         repeat (rewrite upd_ne; [| reg_neq]);
         first [ exact Hx23 | exact Hx24 | exact Hx25 | exact Hx26 | exact Hx27 ]). }
    { exact Hsame. }
    { assert (HE9a0 : E9 !!! Regidx (mword_of_int 10 : mword 5)
                      = Mf !!! Regidx (mword_of_int 10 : mword 5)).
      { peel_reg. }
      rewrite HE9a0. exact Hpay. }
  Qed.

  (* ================================================================= *)
  (* THE SHARED TAIL (+0x46..+0x50) -- sconf mirror.                     *)
  (* ================================================================= *)
  Lemma wp_walk_tail_sconf (γ : gname) (root_ppn : mword 44) (γa : gname) (Φ : mval -> iProp Σ)
      (mm Mf : regfile) (t tf : ptree) (b0 : mword 44) (K : nat) (lvl : nat) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (22 <= K)%nat ->
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
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn Mf (K - 8)%nat -∗ intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
    kernel_text -∗
    pc_is (mword_of_int (WK + 0x46)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γa (mm !!! Regidx (mword_of_int 4)) -∗
    ( ∀ (mr : regfile) (t' : ptree),
      sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap_gpr γ root_ppn mr K -∗ intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γa (mm !!! Regidx (mword_of_int 4)) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ptree_same_rep0 t t'⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
        \/ (exists p2 p1 w0,
             ptree_level0 t' vpn p2 p1 w0 /\
             mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va vpn sp0 spr ret_tgt HK Hva' Hsp Hs3 Hs1 Htp Hx23 Hx24 Hx25 Hx26 Hx27 Hsame Hlvl.
    iIntros "Hsc Hhs Hcg Hcnt Htlbinv #Htext Hpc
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hptree Henv Hcont".
    iPoseProof (wi_46 with "Htext") as "Hi46".
    iPoseProof (wi_4a with "Htext") as "Hi4a".
    iPoseProof (wi_4e with "Htext") as "Hi4e".
    iPoseProof (wi_50 with "Htext") as "Hi50".
    (* +0x46 srli a0,s3,12 *)
    iApply (wp_srli4_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x46)) (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 12 : mword 6)
              Mf (K - 8)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi46 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (T1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (shift_bits_right (Mf !!! Regidx (mword_of_int 19 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> Mf).
    assert (Hpp4a : add_vec_int (mword_of_int (WK + 0x46) : mword 64) 4 = mword_of_int (WK + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* +0x4a andi a0,a0,511 *)
    iApply (wp_andi_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x4a)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 511 : mword 12)
              (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                       (sign_extend' 64 (mword_of_int 511 : mword 12)))
              T1 (K - 8)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite /T1 upd_eq; rewrite Hs3; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi4a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (T2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (mword_of_int 511 : mword 12)))]> T1).
    assert (Hpp4e : add_vec_int (mword_of_int (WK + 0x4a) : mword 64) 4 = mword_of_int (WK + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    (* +0x4e c.slli a0,3 *)
    iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x4e)) (Regidx (mword_of_int 10 : mword 5)) (mword_of_int 10 : mword 5) (mword_of_int 3 : mword 6)
              T2 (K - 8)%nat
              ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi4e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (T3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (shift_bits_left (T2 !!! Regidx (mword_of_int 10 : mword 5)) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> T2).
    assert (Hpp50 : add_vec_int (mword_of_int (WK + 0x4e) : mword 64) 2 = mword_of_int (WK + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 c.add a0,s1 *)
    iApply (wp_cadd_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x50)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              T3 (K - 8)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi50 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (T4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (T3 !!! Regidx (mword_of_int 10 : mword 5)) (T3 !!! Regidx (mword_of_int 9 : mword 5)))]> T3).
    assert (Hpp52 : add_vec_int (mword_of_int (WK + 0x50) : mword 64) 2 = mword_of_int (WK + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52) in "Hpc".
    assert (HT2a0 : T2 !!! Regidx (mword_of_int 10 : mword 5)
        = and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (mword_of_int 511 : mword 12)))
      by (rewrite /T2 upd_eq; reflexivity).
    assert (HT3s1 : T3 !!! Regidx (mword_of_int 9 : mword 5)
                    = zero_extend' 64 (concat_vec b0 (zeros' 12 : mword 12))).
    { rewrite /T3 /T2 /T1.
      repeat (rewrite upd_ne; [| reg_neq]).
      exact Hs1. }
    assert (HT4a0 : T4 !!! Regidx (mword_of_int 10 : mword 5)
                    = u_pte_addr b0 (vpn_idx 0 vpn)).
    { rewrite /T4 upd_eq.
      rewrite {1}/T3 upd_eq.
      rewrite HT2a0 HT3s1.
      replace (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
        with (subrange_vec_dec (mword_of_int 12 : mword 64) (Z.sub log2_xlen 1) 0)
        by (apply bv_eq; vm_compute; reflexivity).
      exact (walk_slot_addr0 b0 va Hva'). }
    (* funnel into the shared epilogue *)
    iApply (wp_walk_epilogue_sconf γ root_ppn γa Φ mm T4 t tf K lvl HK
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    exact Hsp)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    exact Htp)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    exact Hx23)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    exact Hx24)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    exact Hx25)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    exact Hx26)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    exact Hx27)
              Hsame
              ltac:(destruct Hlvl as (p2 & p1 & w0 & Hl0 & Heq);
                    right; exists p2, p1, w0; split;
                    [exact Hl0 | rewrite HT4a0 Heq; reflexivity])
              with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc
                    Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                    Hptree Henv Hcont").
  Qed.

  (* ================================================================= *)
  (* THE LOOP BODY'S STRAIGHT-LINE CORE (+0x26..+0x36) -- sconf mirror.  *)
  (* ================================================================= *)
  Lemma wp_walk_probe_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (M : regfile) (n : nat) (va shift : mword 64) (slotaddr pte : mword 64) {dqm : dfrac} :
    M !!! Regidx (mword_of_int 19 : mword 5) = va ->
    M !!! Regidx (mword_of_int 20 : mword 5) = shift ->
    add_vec
      (shift_bits_left
         (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                  (sign_extend' 64 (mword_of_int 511 : mword 12)))
         (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
      (M !!! Regidx (mword_of_int 9 : mword 5)) = slotaddr ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn M n -∗ tlb_inv_pt root_ppn -∗
    kernel_text -∗
    pc_is (mword_of_int (WK + 0x26)) -∗
    slotaddr ↦₈{dqm} pte -∗
    ( sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap_gpr γ root_ppn (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (and_vec pte (sign_extend' 64 (mword_of_int 1 : mword 12)))]>
                (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg pte]>
                 (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg slotaddr]> M))) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (mword_of_int (WK + 0x3a)) -∗
      slotaddr ↦₈{dqm} pte -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hs3 Hs4 Hslot.
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc Hown Hcont".
    iPoseProof (wi_26 with "Htext") as "Hi26".
    iPoseProof (wi_2a with "Htext") as "Hi2a".
    iPoseProof (wi_2e with "Htext") as "Hi2e".
    iPoseProof (wi_30 with "Htext") as "Hi30".
    iPoseProof (wi_32 with "Htext") as "Hi32".
    iPoseProof (wi_36 with "Htext") as "Hi36".
    (* +0x26 srl s2,s3,s4 *)
    iApply (wp_srl_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x26)) (mword_of_int 18 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 20 : mword 5)
              (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
              M n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3 Hs4; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi26 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (L1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))]> M).
    assert (Hpp2a : add_vec_int (mword_of_int (WK + 0x26) : mword 64) 4 = mword_of_int (WK + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a andi s2,s2,511 *)
    iApply (wp_andi_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x2a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 511 : mword 12)
              (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                       (sign_extend' 64 (mword_of_int 511 : mword 12)))
              L1 n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite /L1 upd_eq; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (L2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (mword_of_int 511 : mword 12)))]> L1).
    assert (Hpp2e : add_vec_int (mword_of_int (WK + 0x2a) : mword 64) 4 = mword_of_int (WK + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.slli s2,3 *)
    iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x2e)) (Regidx (mword_of_int 18 : mword 5)) (mword_of_int 18 : mword 5) (mword_of_int 3 : mword 6)
              L2 n
              ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (L3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_left (L2 !!! Regidx (mword_of_int 18 : mword 5)) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> L2).
    assert (Hpp30 : add_vec_int (mword_of_int (WK + 0x2e) : mword 64) 2 = mword_of_int (WK + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.add s2,s1 *)
    iApply (wp_cadd_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x30)) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
              L3 n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi30 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp32 : add_vec_int (mword_of_int (WK + 0x30) : mword 64) 2 = mword_of_int (WK + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* collapse s2's four writes (L1..L4, all reg18) to ONE insert over M *)
    set (L4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg slotaddr]> M).
    assert (H18 : L3 !!! Regidx (mword_of_int 18 : mword 5) =
        shift_bits_left (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0)) (sign_extend' 64 (mword_of_int 511 : mword 12)))
          (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)).
    { rewrite /L3 upd_eq /L2 upd_eq. reflexivity. }
    assert (H9 : L3 !!! Regidx (mword_of_int 9 : mword 5) = M !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /L3 /L2 /L1. do 3 (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HL4c : <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (add_vec (L3 !!! Regidx (mword_of_int 18 : mword 5)) (L3 !!! Regidx (mword_of_int 9 : mword 5)))]> L3 = L4).
    { rewrite H18 H9. rewrite /L4 /L3 /L2 /L1 !upd_upd. do 2 f_equal. exact Hslot. }
    iEval (rewrite HL4c) in "Hcg".
    assert (HL4s2 : L4 !!! Regidx (mword_of_int 18 : mword 5) = slotaddr)
      by (rewrite /L4 upd_eq; reflexivity).
    assert (Hea0 : forall X : mword 64, add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* +0x32 ld s1,0(s2) *)
    iApply (wp_ld_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
              L4 n pte (dqm:=dqm)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi32 [Hown] [-]").
    { iEval (rewrite Hea0 HL4s2). iExact "Hown". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hown".
    iEval (rewrite Hea0 HL4s2) in "Hown".
    set (L5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg pte]> L4).
    assert (Hpp36 : add_vec_int (mword_of_int (WK + 0x32) : mword 64) 4 = mword_of_int (WK + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 andi a5,s1,1 *)
    iApply (wp_andi_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
              (and_vec pte (sign_extend' 64 (mword_of_int 1 : mword 12)))
              L5 n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite /L5 upd_eq; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi36 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp3a : add_vec_int (mword_of_int (WK + 0x36) : mword 64) 4 = mword_of_int (WK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    iApply ("Hcont" with "Hsc Hhs Hcg Htlbinv Hpc Hown").
  Qed.

  (* ===== memset-zero page wrapper (keeps the zeroed bytes) ===== *)
  Lemma wp_memset_page_zero_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat) (cval : mword 64) :
    let a0_idx : mword 5 := mword_of_int 10 in
    let a1_idx : mword 5 := mword_of_int 11 in
    let a2_idx : mword 5 := mword_of_int 12 in
    let pcE := mword_of_int MS in
    let sp0 := m0 !!! Regidx csp_rs1 in
    let ra0 := m0 !!! Regidx (mword_of_int 1 : mword 5) in
    let p := m0 !!! Regidx a0_idx in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    let cbyte := nth_byte (autocast (T := mword) (subrange_vec_dec cval (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 in
    page_valid p ->
    m0 !!! Regidx a1_idx = cval ->
    m0 !!! Regidx a2_idx = (mword_of_int 4096 : mword 64) ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    (2 <= n)%nat ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m0 n -∗ tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is pcE -∗
    page_own p -∗
    ( ∀ mfin,
      sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap_gpr γ root_ppn mfin n -∗ tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      ([∗ list] j ∈ seq 0 4096, (pa_add p j) ↦ₘ cbyte) -∗
      ⌜ callee_saved m0 mfin ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros a0_idx a1_idx a2_idx pcE sp0 ra0 p ret_tgt cbyte Hpv Hcval Ha2 Hret0 Hn.
    set (ra_idx := (mword_of_int 1 : mword 5)).
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (a4_idx := (mword_of_int 14 : mword 5)).
    set (a5_idx := (mword_of_int 15 : mword 5)).
    set (imm_entry := (mword_of_int 48 : mword 6)).
    set (shamt_l := (mword_of_int 32 : mword 6)).
    set (shamt_r := (mword_of_int 32 : mword 6)).
    set (nzimm_s0 := (mword_of_int 4 : mword 8)).
    set (imm8_beqz := (mword_of_int 11 : mword 8)).
    set (imm_bne := (mword_of_int 0x1ffa : mword 13)).
    set (wval_add := add_vec (mword_of_int 4096 : mword 64) p).
    set (s00 := m0 !!! Regidx s0_idx).
    set (sp' := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1).
    set (m3 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2).
    set (m4 := <[Regidx a2_idx := regval_into_reg (shift_bits_left (m3 !!! Regidx a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3).
    set (m5 := <[Regidx a2_idx := regval_into_reg (shift_bits_right (m4 !!! Regidx a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4).
    set (m6 := <[Regidx a4_idx := regval_into_reg wval_add]> m5).
    pose proof (add_vec_frame_cancel) as Hframe.
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc Hpage Hcont".
    (* --- bridge [page_own p] to memset's per-byte buffer --- *)
    iEval (rewrite /page_own /byte_any) in "Hpage".
    iDestruct (bytes_choose 4096 0 (fun j b => ((pa_add p j) ↦ₘ b)%I) with "Hpage")
      as (olds) "Hpage".
    iAssert ([∗ list] j ∈ seq 0 4096, (ms_pa (ms_addr p j)) ↦ₘ olds j)%I
      with "[Hpage]" as "Hbuf".
    { iApply (big_sepL_impl with "Hpage"). iIntros "!>" (k j _) "H".
      rewrite ms_pa_ms_addr. iExact "H". }
    (* --- prefix/loop/suffix instr resources --- *)
    iPoseProof (minstr_cba with "Htext") as "Hi0".
    iPoseProof (minstr_cbc with "Htext") as "Hi2".
    iPoseProof (minstr_cbe with "Htext") as "Hi4".
    iPoseProof (minstr_cc0 with "Htext") as "Hi6".
    iPoseProof (minstr_cc2 with "Htext") as "Hi8".
    iPoseProof (minstr_cc4 with "Htext") as "Hi10".
    iPoseProof (minstr_cc6 with "Htext") as "Hi12".
    iPoseProof (minstr_cc8 with "Htext") as "Hi14".
    iPoseProof (minstr_cca with "Htext") as "Hi16".
    iPoseProof (minstr_cd8 with "Htext") as "HiL0".
    iPoseProof (minstr_cda with "Htext") as "HiL2".
    iPoseProof (minstr_cdc with "Htext") as "HiL4".
    iPoseProof (minstr_cde with "Htext") as "HiL6".
    (* the value-coupling premises for the prefix and the loop *)
    assert (Hn0 : eq_vec (m0 !!! Regidx a2_idx) zero_reg = false)
      by (rewrite Ha2; vm_compute; reflexivity).
    assert (Hvalue_add : add_vec (m5 !!! Regidx a2_idx) (m5 !!! Regidx a0_idx) = wval_add).
    { assert (HA : m5 !!! Regidx a2_idx = (mword_of_int 4096 : mword 64)).
      { unfold m5, m4, m3.
        rewrite upd_eq.
        rewrite upd_eq.
        unfold m2, m1.
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite Ha2. apply bv_eq; vm_compute; reflexivity. }
      assert (HB : m5 !!! Regidx a0_idx = p).
      { unfold m5, m4, m3, m2, m1.
        repeat (rewrite upd_ne; [| vm_compute; discriminate]).
        reflexivity. }
      rewrite HA HB. reflexivity. }
    assert (Hsp' : sp' = pa_stk sp0 2).
    { unfold sp', imm_entry, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    (* --- PREFIX: 0x00..0x10 --- *)
    iApply (Memset.wp_memset_prefix_sconf γ root_ppn Φ m0 n imm_entry shamt_l shamt_r nzimm_s0 imm8_beqz
              wval_add ltac:(lia) Hsp' Hn0 Hvalue_add
              with "Hsc Hhs Hcg Htlbinv Hpc
                    Hi0 Hi2 Hi4 Hi6 Hi8 Hi10 Hi12 Hi14 Hi16 [-]").
    iIntros "Hsc Hhs Hcg Htlbinv Hpc Hbra Hbs0".
    change (<[Regidx a4_idx := regval_into_reg wval_add]> m5) with m6.
    (* pc at pcE+20 = memset+0x14 = loop top *)
    assert (Hpc1 : add_vec_int pcE 20 = mword_of_int (MS + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1) in "Hpc".
    (* loop-entry facts on m6 *)
    assert (Hcur : m6 !!! Regidx a5_idx = ms_addr p 0).
    { unfold m6, m5, m4, m3.
      rewrite upd_ne; [| vm_compute; discriminate].
      rewrite upd_ne; [| vm_compute; discriminate].
      rewrite upd_ne; [| vm_compute; discriminate].
      rewrite upd_eq.
      unfold regval_into_reg. rewrite add_vec_zero_l.
      unfold m2, m1.
      rewrite upd_ne; [| vm_compute; discriminate].
      rewrite upd_ne; [| vm_compute; discriminate].
      unfold ms_addr, p. change (Z.of_nat 0) with 0%Z. symmetry. exact (RiscvExtras.avi0 (m0 !!! Regidx a0_idx)). }
    assert (Hm4 : m6 !!! Regidx a4_idx = wval_add)
      by (unfold m6; rewrite upd_eq; unfold regval_into_reg; reflexivity).
    assert (Hm1 : m6 !!! Regidx a1_idx = cval).
    { unfold m6, m5, m4, m3, m2, m1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite -Hcval. reflexivity. }
    (* --- LOOP: 0x14..0x1a --- *)
    iApply (Memset.wp_memset_loop_sconf γ root_ppn Φ 4096 p wval_add cval a1_idx a4_idx a5_idx imm_bne
              olds (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(intros j; exact (ms_incr_step p j))
              ltac:(intros j Hj; exact (ms_cmp_page p j Hpv Hj))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              minstr_cce minstr_cd2 minstr_cd4
              4096%nat 0%nat m6 ltac:(reflexivity) ltac:(lia) Hcur Hm4 Hm1
              with "Hsc Hhs Hcg Htlbinv Htext Hpc Hbuf [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbuf".
    set (m7 := <[Regidx a5_idx := regval_into_reg (ms_addr p 4096)]> m6).
    change (<[Regidx a5_idx := regval_into_reg (ms_addr p 4096)]> m6) with m7.
    assert (Hpc2 : add_vec_int (add_vec_int (mword_of_int (MS + 0x14) : mword 64) 6) 4 = (mword_of_int (MS + 0x1e) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2) in "Hpc".
    (* --- SUFFIX: 0x1e..0x24 --- *)
    assert (Hsuf_sp : m7 !!! Regidx csp_rs1 = sp').
    { unfold m7, m6, m5, m4, m3, m2.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold m1. rewrite upd_eq. reflexivity. }
    assert (Hsuf_ra : m7 !!! Regidx (mword_of_int 1 : mword 5) = ra0).
    { unfold m7, m6, m5, m4, m3, m2, m1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold ra0; reflexivity. }
    iApply (Memset.wp_memset_suffix_sconf γ root_ppn Φ m7 (n - 2)%nat ra0 s00
              Hret0
              with "Hsc Hhs Hcg Htlbinv HiL0 HiL2 HiL4 HiL6 Hpc [Hbra] [Hbs0] [-]").
    { iEval (rewrite Hsuf_sp). iExact "Hbra". }
    { iEval (rewrite Hsuf_sp). iExact "Hbs0". }
    iIntros (mfin) "Hhs Hsc Hcg Htlbinv Hpc %Hmeq".
    assert (Hn2fix : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hn2fix) in "Hcg".
    (* hand the all-cbyte buffer back directly (KEEP the written bytes) *)
    iApply ("Hcont" $! mfin with "Hsc Hhs Hcg Htlbinv Hpc [Hbuf] [%]").
    - iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H".
      iEval (rewrite ms_pa_ms_addr) in "H". iExact "H".
    - (* callee_saved m0 mfin: only sp/s0 moved *)
      assert (Hcatch : forall r : regidx,
                r <> Regidx (mword_of_int 1 : mword 5) -> r <> Regidx s0_idx -> r <> Regidx csp_rs1 ->
                r <> Regidx a5_idx -> r <> Regidx a2_idx -> r <> Regidx a4_idx ->
                m7 !!! r = m0 !!! r).
      { intros r Hra Hs0 Hcsp Ha5 Ha2r Ha4.
        unfold m7, m6, m5, m4, m3, m2, m1.
        rewrite upd_ne; [| exact Ha5].
        rewrite upd_ne; [| exact Ha4].
        rewrite upd_ne; [| exact Ha2r].
        rewrite upd_ne; [| exact Ha2r].
        rewrite upd_ne; [| exact Ha5].
        rewrite upd_ne; [| exact Hs0].
        rewrite upd_ne; [| exact Hcsp].
        reflexivity. }
      rewrite Hmeq.
      unfold callee_saved. repeat apply conj.
      + rewrite upd_eq. rewrite Hsuf_sp.
        unfold sp', imm_entry. apply Hframe.
      + rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_ne; [| vm_compute; discriminate].
        apply Hcatch; vm_compute; discriminate.
      + rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_eq.
        unfold s00, s0_idx. reflexivity.
      + rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        apply Hcatch; vm_compute; discriminate.
      + rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        apply Hcatch; vm_compute; discriminate.
      + rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        apply Hcatch; vm_compute; discriminate.
      + rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        apply Hcatch; vm_compute; discriminate.
      + rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        apply Hcatch; vm_compute; discriminate.
      + rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        apply Hcatch; vm_compute; discriminate.
      + rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        apply Hcatch; vm_compute; discriminate.
      + rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        apply Hcatch; vm_compute; discriminate.
      + rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        apply Hcatch; vm_compute; discriminate.
      + rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        apply Hcatch; vm_compute; discriminate.
      + rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        rewrite upd_ne; [| vm_compute; discriminate];
        apply Hcatch; vm_compute; discriminate.
  Qed.

  (* ================================================================= *)
  (* THE SHARED ALLOCATION ARM (+0x72..+0x94) -- sconf mirror.           *)
  (* ================================================================= *)
  Lemma wp_walk_alloc_sconf (γ : gname) (root_ppn : mword 44) (γa : gname) (Φ : mval -> iProp Σ)
      (mm Mf : regfile) (t tf : ptree)
      (tG : mword 44 -> ptree) (clvl : nat)
      (cellA : mword 64) (w0 : bv 64) (K : nat) (lvl : nat) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    lvl = 0%nat ->
    (22 <= K)%nat ->
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
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn Mf (K - 8)%nat -∗ intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
    kernel_text -∗
    pc_is (mword_of_int (WK + 0x72)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γa (mm !!! Regidx (mword_of_int 4)) -∗
    ( ∀ (Mo : regfile) (b : mword 44),
      ⌜forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
         Mo !!! Regidx c = Mf !!! Regidx c⌝ -∗
      ⌜Mo !!! Regidx (mword_of_int 9 : mword 5)
         = zero_extend' 64 (concat_vec b (zeros' 12 : mword 12))⌝ -∗
      sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap_gpr γ root_ppn Mo (K - 8)%nat -∗ intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
      pc_is (mword_of_int (WK + 0x40)) -∗
      pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
      pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
      pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
      pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
      pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
      pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
      pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
      pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
      ptree_own 2 (DfracOwn 1) (tG b) -∗
      kalloc_env γa (mm !!! Regidx (mword_of_int 4)) -∗
      ( ∀ (mr : regfile) (t' : ptree),
        sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        sie_cap_gpr γ root_ppn mr K -∗ intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
        pc_is ret_tgt -∗
        ptree_own 2 (DfracOwn 1) t' -∗
        kalloc_env γa (mm !!! Regidx (mword_of_int 4)) -∗
        ⌜callee_saved mm mr⌝ -∗
        ⌜ptree_same_rep0 t t'⌝ -∗
        ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
          \/ (exists p2 p1 w1,
               ptree_level0 t' vpn p2 p1 w1 /\
               mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    ( ∀ (mr : regfile) (t' : ptree),
      sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap_gpr γ root_ppn mr K -∗ intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γa (mm !!! Regidx (mword_of_int 4)) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ptree_same_rep0 t t'⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
        \/ (exists p2 p1 w1,
             ptree_level0 t' vpn p2 p1 w1 /\
             mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va vpn sp0 spr ret_tgt Hlvl HK Hsp Hs2c Hs6 Htp Hx23 Hx24 Hx25 Hx26 Hx27 Hsame Hacc.
    iIntros "Hsc Hhs Hcg Hcnt Htlbinv #Htext Hpc
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hptree Henv Hok Hcont".
    iPoseProof (wi_72 with "Htext") as "Hi72".
    iPoseProof (wi_76 with "Htext") as "Hi76".
    iPoseProof (wi_7a with "Htext") as "Hi7a".
    iPoseProof (wi_7c with "Htext") as "Hi7c".
    (* +0x72 beqz s6 FALLS (alloc = 1) *)
    iApply (wp_beqz_x0_fall_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x72)) (mword_of_int 36 : mword 13) (mword_of_int 22 : mword 5)
              Mf (K - 8)%nat ltac:(vm_compute; discriminate) Hs6
              with "Hsc Hhs Hcg Htlbinv Hpc Hi72 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp76 : add_vec_int (mword_of_int (WK + 0x72) : mword 64) 4 = mword_of_int (WK + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp76) in "Hpc".
    (* +0x76 jal kalloc *)
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x76)) (mword_of_int 1 : mword 5) (mword_of_int 2095964 : mword 21)
              Mf (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi76 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (J := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (WK + 0x76) : mword 64) 4)]> Mf).
    assert (Htgtk : add_vec (mword_of_int (WK + 0x76) : mword 64) (sign_extend' 64 (mword_of_int 2095964 : mword 21)) = mword_of_int KernelSyms.kalloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtk) in "Hpc".
    (* ---- kalloc() through the env bundle ---- *)
    iDestruct "Henv" as (γk qint qcpu) "(%Hqne & %H0ne & #Hlock & #Havail & Hnoff & Hint & Hqcpu)".
    assert (HspJ : J !!! Regidx csp_rs1 = spr).
    { rewrite /J. rewrite upd_ne; [| reg_neq]. exact Hsp. }
    assert (HJ4 : J !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite /J. rewrite upd_ne; [| reg_neq]. exact Htp. }
    assert (HJ1 : J !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (WK + 0x76) : mword 64) 4)
      by (rewrite /J upd_eq; reflexivity).
    assert (Hretk : eq_vec (access_vec_dec (update_vec_dec (add_vec (J !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true).
    { rewrite HJ1. vm_compute. reflexivity. }
    iApply (Kalloc.wp_kalloc_sconf γ root_ppn Φ γa γk (mword_of_int (KernelSyms.kmem + 24))
              J qcpu (zeros' 32 : mword 32) qint None lvl (K - 8)%nat
              ltac:(lia)
              ltac:(rewrite HJ4; exact Hqne)
              Hretk
              ltac:(reflexivity)
              ltac:(split; [intros _; exact Hlvl | intros _; vm_compute; reflexivity])
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc [Hlock] Havail [Hnoff] [Hint] [Hqcpu] [-]").
    { iExact "Hlock". }
    { iEval (rewrite HJ4). iExact "Hnoff". }
    { iEval (rewrite HJ4). iExact "Hint". }
    { iExact "Hqcpu". }
    iIntros (mr) "Hsc Hhs Hcg Hcnt Htlbinv Hpc %Hkcs Hkpost Hcpu2 Hnoff2 Hint2".
    (* the return pc: +0x7a *)
    assert (Hret7a : update_vec_dec (add_vec (J !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0" : mword 1) = mword_of_int (WK + 0x7a)).
    { rewrite HJ1. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret7a) in "Hpc".
    (* +0x7a c.mv s1,a0 *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x7a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mr (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi7a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (N1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mr !!! Regidx (mword_of_int 10 : mword 5)))]> mr).
    assert (Hpp7c : add_vec_int (mword_of_int (WK + 0x7a) : mword 64) 2 = mword_of_int (WK + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7c) in "Hpc".
    (* rebuild kalloc_env from the returned cells *)
    assert (Hnr : (autocast (T := mword) (subrange_vec_dec
        (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64
           (autocast (T := mword) (subrange_vec_dec
              (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 (zeros' 32 : mword 32)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
              (Z.sub (Z.mul 4 8) 1) 0) : mword 32))
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
        (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = (zeros' 32 : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    iDestruct "Hint2" as (qint2) "Hint2".
    iAssert (kalloc_env γa (mm !!! Regidx (mword_of_int 4)))
      with "[Hcpu2 Hnoff2 Hint2]" as "Henv".
    { iExists γk, qint2, (zero_reg : mword 64).
      iSplitR. { iPureIntro. exact H0ne. }
      iSplitR. { iPureIntro. exact H0ne. }
      iFrame "Hlock". iFrame "Havail".
      iSplitL "Hnoff2".
      { iEval (rewrite HJ4 Hnr) in "Hnoff2". iExact "Hnoff2". }
      iSplitL "Hint2". { iEval (rewrite HJ4) in "Hint2". iExact "Hint2". }
      iExact "Hcpu2". }
    (* +0x7c c.beqz a0: the null/success split *)
    iDestruct "Hkpost" as "[(%Hnull & _ & _) | (%Hpv & Hpage & _)]".
    { (* ---- NULL: exit through the epilogue with a0 = 0 ---- *)
      assert (HN1a0 : N1 !!! Regidx (mword_of_int 10 : mword 5) = mr !!! Regidx (mword_of_int 10 : mword 5)).
      { rewrite /N1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iApply (wp_cbeqz_taken_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x7c)) (mword_of_int 235 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
                N1 (K - 8)%nat
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HN1a0 Hnull; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi7c [-]").
      iNext. iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Htgt52 : add_vec (mword_of_int (WK + 0x7c) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 235 : mword 8) ('b"0"))))
              = mword_of_int (WK + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt52) in "Hpc".
      iApply (wp_walk_epilogue_sconf γ root_ppn γa Φ mm N1 t tf K lvl HK
                ltac:(rewrite /N1; rewrite upd_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (csp_rs1 : mword 5)
                                 ltac:(vm_compute; reflexivity));
                      exact HspJ)
                ltac:(rewrite /N1; rewrite upd_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 4)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite upd_ne; [| reg_neq];
                      exact Htp)
                ltac:(rewrite /N1; rewrite upd_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 23)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite upd_ne; [| reg_neq];
                      exact Hx23)
                ltac:(rewrite /N1; rewrite upd_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 24)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite upd_ne; [| reg_neq];
                      exact Hx24)
                ltac:(rewrite /N1; rewrite upd_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 25)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite upd_ne; [| reg_neq];
                      exact Hx25)
                ltac:(rewrite /N1; rewrite upd_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 26)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite upd_ne; [| reg_neq];
                      exact Hx26)
                ltac:(rewrite /N1; rewrite upd_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 27)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite upd_ne; [| reg_neq];
                      exact Hx27)
                Hsame
                ltac:(left; rewrite HN1a0 Hnull; reflexivity)
                with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hptree Henv Hcont"). }
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
    { rewrite /N1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hnz : (zero_reg : mword 64) = nullp) by (apply bv_eq; vm_compute; reflexivity).
    pose proof Hpv as Hpv'.
    destruct Hpv' as [Hal Hrange]. unfold page_in_range, kmem_lo, kmem_hi in Hrange.
    unfold page_aligned, PGSIZE in Hal.
    assert (Hlt56 : uint (mr !!! Regidx (mword_of_int 10 : mword 5)) < 72057594037927936) by lia.
    set (bppn := (autocast (T := mword) (subrange_vec_dec (mr !!! Regidx (mword_of_int 10 : mword 5)) 55 12) : mword 44)).
    assert (Hpb : zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))
                  = mr !!! Regidx (mword_of_int 10 : mword 5))
      by (exact (walk_alloc_page_base _ Hal Hlt56)).
    (* +0x7c c.beqz a0 FALLS (p <> 0) *)
    iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x7c)) (mword_of_int 235 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              N1 (K - 8)%nat
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite HN1a0; apply eq_vec_false_iff; rewrite Hnz;
                    exact (page_valid_ne_null _ Hpv))
              with "Hsc Hhs Hcg Htlbinv Hpc Hi7c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp7e : add_vec_int (mword_of_int (WK + 0x7c) : mword 64) 2 = mword_of_int (WK + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7e) in "Hpc".
    (* +0x7e c.lui a2,1 *)
    iApply (wp_clui_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x7e)) (mword_of_int 12 : mword 5)
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              N1 (K - 8)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi7e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (N2 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 4096 : mword 64)]> N1).
    assert (Hpp80 : add_vec_int (mword_of_int (WK + 0x7e) : mword 64) 2 = mword_of_int (WK + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp80) in "Hpc".
    (* +0x80 c.li a1,0 *)
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x80)) (mword_of_int 11 : mword 5) (mword_of_int 0 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
              N2 (K - 8)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi80 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (N3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> N2).
    assert (Hpp82 : add_vec_int (mword_of_int (WK + 0x80) : mword 64) 2 = mword_of_int (WK + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp82) in "Hpc".
    (* +0x82 jal memset *)
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x82)) (mword_of_int 1 : mword 5) (mword_of_int 2096362 : mword 21)
              N3 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi82 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (N4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (WK + 0x82) : mword 64) 4)]> N3).
    assert (Htgtm : add_vec (mword_of_int (WK + 0x82) : mword 64) (sign_extend' 64 (mword_of_int 2096362 : mword 21)) = mword_of_int KernelSyms.memset)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtm) in "Hpc".
    (* memset(p, 0, 4096) keeping the zero bytes *)
    assert (HN4a0 : N4 !!! Regidx (mword_of_int 10 : mword 5) = mr !!! Regidx (mword_of_int 10 : mword 5)).
    { peel_reg. }
    assert (HspN4 : N4 !!! Regidx csp_rs1 = spr).
    { rewrite /N4 /N3 /N2 /N1.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite (callee_saved_lookup Hkcs (csp_rs1 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HspJ. }
    iApply (wp_memset_page_zero_sconf γ root_ppn Φ N4 (K - 8)%nat (mword_of_int 0 : mword 64)
              ltac:(rewrite HN4a0; exact Hpv)
              ltac:(rewrite /N4; rewrite upd_ne; [| reg_neq];
                    rewrite /N3 upd_eq; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /N4 /N3;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    rewrite upd_eq; reflexivity)
              ltac:(rewrite /N4 upd_eq; vm_compute; reflexivity)
              ltac:(lia)
              with "Hsc Hhs Hcg Htlbinv Htext Hpc [Hpage] [-]").
    { iEval (rewrite HN4a0). iExact "Hpage". }
    iIntros (mfin) "Hsc Hhs Hcg Htlbinv Hpc Hbytes %Hmcs".
    assert (Hret86 : update_vec_dec (add_vec (N4 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0" : mword 1) = mword_of_int (WK + 0x86)).
    { rewrite /N4 upd_eq. apply bv_eq; vm_compute; reflexivity. }
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
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /N1 upd_eq. reflexivity. }
    iApply (wp_srli4_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x86)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
              mfin (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi86 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (P1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (mfin !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> mfin).
    assert (Hpp8a : add_vec_int (mword_of_int (WK + 0x86) : mword 64) 4 = mword_of_int (WK + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8a) in "Hpc".
    (* +0x8a c.slli a5,10 *)
    iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x8a)) (Regidx (mword_of_int 15 : mword 5)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 6)
              P1 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi8a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (P2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (P1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> P1).
    assert (Hpp8c : add_vec_int (mword_of_int (WK + 0x8a) : mword 64) 2 = mword_of_int (WK + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8c) in "Hpc".
    (* +0x8c ori a5,a5,1 *)
    iApply (wp_ori_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x8c)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 12)
              (or_vec (P2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
              P2 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi8c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (P3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (or_vec (P2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> P2).
    assert (Hpp90 : add_vec_int (mword_of_int (WK + 0x8c) : mword 64) 4 = mword_of_int (WK + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp90) in "Hpc".
    assert (HP3a5 : P3 !!! Regidx (mword_of_int 15 : mword 5) = pt_ptr_pte bppn).
    { rewrite /P3 upd_eq.
      rewrite {1}/P2 upd_eq.
      rewrite {1}/P1 upd_eq.
      rewrite Hmfs1 add_vec_zero_l.
      exact (walk_alloc_pte _ Hal Hlt56). }
    (* +0x90 sd a5,0(s2): the pointer-PTE store through the graft cell *)
    assert (HP3s2 : P3 !!! Regidx (mword_of_int 18 : mword 5) = cellA).
    { rewrite /P3 /P2 /P1.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite (callee_saved_lookup Hmcs (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite /N4 /N3 /N2 /N1.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite (callee_saved_lookup Hkcs (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite /J. rewrite upd_ne; [| reg_neq].
      exact Hs2c. }
    assert (Hea0' : forall X : mword 64, add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iDestruct (Hacc with "Hptree") as "[Hcell Hgw]".
    iApply (wp_sd_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x90)) (mword_of_int 15 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
              P3 (K - 8)%nat w0
              with "Hsc Hhs Hcg Htlbinv Hpc Hi90 [Hcell] [-]").
    { iEval (rewrite Hea0' HP3s2). iExact "Hcell". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hcell".
    iEval (rewrite Hea0' HP3s2 HP3a5) in "Hcell".
    iDestruct ("Hgw" $! bppn with "Hcell Hchild") as "Hptree".
    assert (Hpp94 : add_vec_int (mword_of_int (WK + 0x90) : mword 64) 4 = mword_of_int (WK + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp94) in "Hpc".
    (* +0x94 c.j back to the loop decrement at +0x40 *)
    iApply (wp_cj_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x94))
              (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0")))
              P3 (K - 8)%nat ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi94 [-]").
    iNext. iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Htgt40 : add_vec (mword_of_int (WK + 0x94) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0"))))
            = mword_of_int (WK + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt40) in "Hpc".
    (* hand off to the success continuation *)
    iApply ("Hok" $! P3 bppn with "[%] [%] Hsc Hhs Hcg Hcnt Htlbinv Hpc
            Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hptree Henv Hcont").
    { intros c Hcs Hc9.
      rewrite /P3 /P2 /P1.
      repeat (rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hcs; discriminate]).
      rewrite (callee_saved_lookup Hmcs c Hcs).
      rewrite /N4 /N3 /N2.
      repeat (rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hcs; discriminate]).
      rewrite /N1.
      rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; exact (Hc9 Habs2)].
      rewrite (callee_saved_lookup Hkcs c Hcs).
      rewrite /J.
      rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hcs; discriminate].
      reflexivity. }
    { rewrite /P3 /P2 /P1.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite Hmfs1 add_vec_zero_l.
      symmetry. exact Hpb. }
  Qed.



  (* ================================================================= *)
  (* THE TOP-LEVEL walk() WP -- sconf mirror of wp_walk_r.              *)
  (* ================================================================= *)
  Lemma wp_walk_sconf (γ : gname) (root_ppn : mword 44) (γa : gname) (Φ : mval -> iProp Σ)
      (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (K : nat) (lvl : nat)
    : wp_walk_sconf_body γ root_ppn γa Φ mm t m K lvl.
  Proof.
    cbv beta delta [wp_walk_sconf_body].
    intros va vpn sp0 ret_tgt Hlvl HK Ha0 Ha2 Hva Hrep.
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> mm).
    assert (Hsp1 : W1 !!! Regidx csp_rs1 = pa_stk (mm !!! Regidx csp_rs1) 8).
    { rewrite /W1 upd_eq. unfold regval_into_reg, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    iIntros "Hsc Hhs Hcg Hcnt Htlbinv #Htext Hpc Hptree Henv Hcont".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 8 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
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
    (* +0x00 c.addi16sp sp,-64 : the 8-slot frame push *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 8).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf γ root_ppn Φ (mword_of_int WK) (mword_of_int 60 : mword 6) mm K 8 ltac:(lia) Hpush
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> mm) with W1.
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _)".
    iDestruct "S1" as (v56) "Hc56". iDestruct "S2" as (v48) "Hc48".
    iDestruct "S3" as (v40) "Hc40". iDestruct "S4" as (v32) "Hc32".
    iDestruct "S5" as (v24) "Hc24". iDestruct "S6" as (v16) "Hc16".
    iDestruct "S7" as (v08) "Hc08". iDestruct "S8" as (v00) "Hc00".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr)
      by (rewrite /W1 upd_eq; reflexivity).
    assert (Hpp02 : add_vec_int (mword_of_int WK : mword 64) 2 = mword_of_int (WK + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp x1,56(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x02)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 8)%nat v56 with "Hsc Hhs Hcg Htlbinv Hpc Hi02 [Hc56] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc56". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc56".
    assert (Hpp04 : add_vec_int (mword_of_int (WK + 0x02) : mword 64) 2 = mword_of_int (WK + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp x8,48(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x04)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 8)%nat v48 with "Hsc Hhs Hcg Htlbinv Hpc Hi04 [Hc48] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc48". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc48".
    assert (Hpp06 : add_vec_int (mword_of_int (WK + 0x04) : mword 64) 2 = mword_of_int (WK + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp x9,40(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x06)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              W1 (K - 8)%nat v40 with "Hsc Hhs Hcg Htlbinv Hpc Hi06 [Hc40] [-]").
    { iEval (rewrite HspW1 Hb3). iExact "Hc40". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc40".
    assert (Hpp08 : add_vec_int (mword_of_int (WK + 0x06) : mword 64) 2 = mword_of_int (WK + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp x18,32(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x08)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              W1 (K - 8)%nat v32 with "Hsc Hhs Hcg Htlbinv Hpc Hi08 [Hc32] [-]").
    { iEval (rewrite HspW1 Hb4). iExact "Hc32". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc32".
    assert (Hpp0a : add_vec_int (mword_of_int (WK + 0x08) : mword 64) 2 = mword_of_int (WK + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp x19,24(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x0a)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              W1 (K - 8)%nat v24 with "Hsc Hhs Hcg Htlbinv Hpc Hi0a [Hc24] [-]").
    { iEval (rewrite HspW1 Hb5). iExact "Hc24". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc24".
    assert (Hpp0c : add_vec_int (mword_of_int (WK + 0x0a) : mword 64) 2 = mword_of_int (WK + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.sdsp x20,16(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x0c)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              W1 (K - 8)%nat v16 with "Hsc Hhs Hcg Htlbinv Hpc Hi0c [Hc16] [-]").
    { iEval (rewrite HspW1 Hb6). iExact "Hc16". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc16".
    assert (Hpp0e : add_vec_int (mword_of_int (WK + 0x0c) : mword 64) 2 = mword_of_int (WK + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.sdsp x21,8(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x0e)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              W1 (K - 8)%nat v08 with "Hsc Hhs Hcg Htlbinv Hpc Hi0e [Hc08] [-]").
    { iEval (rewrite HspW1 Hb7). iExact "Hc08". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc08".
    assert (Hpp10 : add_vec_int (mword_of_int (WK + 0x0e) : mword 64) 2 = mword_of_int (WK + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.sdsp x22,0(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x10)) (mword_of_int 0 : mword 6) (mword_of_int 22 : mword 5)
              W1 (K - 8)%nat v00 with "Hsc Hhs Hcg Htlbinv Hpc Hi10 [Hc00] [-]").
    { iEval (rewrite HspW1 Hb8). iExact "Hc00". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc00".
    assert (Hpp12 : add_vec_int (mword_of_int (WK + 0x10) : mword 64) 2 = mword_of_int (WK + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.addi4spn s0,sp,64 *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x12)) (Cregidx (mword_of_int 0)) (mword_of_int 16 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 8)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi12 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> W1).
    assert (Hpp14 : add_vec_int (mword_of_int (WK + 0x12) : mword 64) 2 = mword_of_int (WK + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.mv x9,x10 *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x14)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              W2 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi14 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (W3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (W2 !!! Regidx (mword_of_int 10 : mword 5)))]> W2).
    assert (Hpp16 : add_vec_int (mword_of_int (WK + 0x14) : mword 64) 2 = mword_of_int (WK + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 c.mv x19,x11 *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x16)) (mword_of_int 19 : mword 5) (mword_of_int 11 : mword 5)
              W3 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi16 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (W4 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg
        (add_vec zero_reg (W3 !!! Regidx (mword_of_int 11 : mword 5)))]> W3).
    assert (Hpp18 : add_vec_int (mword_of_int (WK + 0x16) : mword 64) 2 = mword_of_int (WK + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.mv x22,x12 *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x18)) (mword_of_int 22 : mword 5) (mword_of_int 12 : mword 5)
              W4 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi18 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (W5 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg
        (add_vec zero_reg (W4 !!! Regidx (mword_of_int 12 : mword 5)))]> W4).
    assert (Hpp1a : add_vec_int (mword_of_int (WK + 0x18) : mword 64) 2 = mword_of_int (WK + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.li a5,-1 *)
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 63 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))
              W5 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (W6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> W5).
    assert (Hpp1c : add_vec_int (mword_of_int (WK + 0x1a) : mword 64) 2 = mword_of_int (WK + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.srli a5,26 *)
    iApply (wp_csrli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x1c)) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) (mword_of_int 26 : mword 6)
              W6 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (W7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (W6 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 26 : mword 6) (Z.sub log2_xlen 1) 0))]> W6).
    assert (Hpp1e : add_vec_int (mword_of_int (WK + 0x1c) : mword 64) 2 = mword_of_int (WK + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.li s4,30 *)
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x1e)) (mword_of_int 20 : mword 5) (mword_of_int 30 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 30 : mword 6))))
              W7 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (W8 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 30 : mword 6))))]> W7).
    assert (Hpp20 : add_vec_int (mword_of_int (WK + 0x1e) : mword 64) 2 = mword_of_int (WK + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 c.li s5,12 *)
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x20)) (mword_of_int 21 : mword 5) (mword_of_int 12 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 12 : mword 6))))
              W8 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi20 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (W9 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 12 : mword 6))))]> W8).
    assert (Hpp22 : add_vec_int (mword_of_int (WK + 0x20) : mword 64) 2 = mword_of_int (WK + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    assert (Hva' : uint va < 274877906944) by (change 274877906944 with (2 ^ 38); exact Hva).
    assert (HW9va : W9 !!! Regidx (mword_of_int 11 : mword 5) = va).
    { peel_reg. }
    assert (HW6a5 : W6 !!! Regidx (mword_of_int 15 : mword 5)
                    = (mword_of_int 18446744073709551615 : mword 64)).
    { rewrite /W6 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HW9a5 : W9 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 274877906943).
    { rewrite /W9 /W8.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /W7 upd_eq. rewrite HW6a5.
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x22 bltu a5,a1 FALLS *)
    iApply (wp_bltu_fall_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x22)) (mword_of_int 68 : mword 13) (mword_of_int 11 : mword 5) (mword_of_int 15 : mword 5)
              W9 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HW9a5 HW9va; unfold zopz0zI_u; apply Z.ltb_ge;
                    replace (uint (mword_of_int 274877906943 : mword 64)) with 274877906943 by (vm_compute; reflexivity);
                    lia)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi22 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
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
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /W4 upd_eq.
      rewrite /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite add_vec_zero_l. reflexivity. }
    assert (HW9s4 : W9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
    { rewrite /W9. rewrite upd_ne; [| reg_neq].
      rewrite /W8 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HW9s1 : W9 !!! Regidx (mword_of_int 9 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /W3 upd_eq.
      rewrite /W2 /W1.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite add_vec_zero_l. rewrite Ha0. reflexivity. }
    assert (Hpp2a : add_vec_int (mword_of_int (WK + 0x26) : mword 64) 4 = mword_of_int (WK + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hpp2e : add_vec_int (mword_of_int (WK + 0x2a) : mword 64) 4 = mword_of_int (WK + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hpp30 : add_vec_int (mword_of_int (WK + 0x2e) : mword 64) 2 = mword_of_int (WK + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hpp32 : add_vec_int (mword_of_int (WK + 0x30) : mword 64) 2 = mword_of_int (WK + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    (* +0x26 srl s2,s3,s4 *)
    iApply (wp_srl_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x26)) (mword_of_int 18 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 20 : mword 5)
              (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
              W9 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HW9s3 HW9s4; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi26 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (L1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))]> W9).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a andi s2,s2,511 *)
    iApply (wp_andi_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x2a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 511 : mword 12)
              (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
                       (sign_extend' 64 (mword_of_int 511 : mword 12)))
              L1 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite /L1 upd_eq; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (L2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (mword_of_int 511 : mword 12)))]> L1).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.slli s2,3 *)
    iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x2e)) (Regidx (mword_of_int 18 : mword 5)) (mword_of_int 18 : mword 5) (mword_of_int 3 : mword 6)
              L2 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (L3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_left (L2 !!! Regidx (mword_of_int 18 : mword 5)) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> L2).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.add s2,s1 *)
    iApply (wp_cadd_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x30)) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
              L3 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi30 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (rewrite Hpp32) in "Hpc".
    (* collapse the four s2-writes into ONE insert over W9 *)
    set (L4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (u_pte_addr (pt_base t) (vpn_idx 2 vpn))]> W9).
    assert (H18a : L3 !!! Regidx (mword_of_int 18 : mword 5) =
        shift_bits_left (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0)) (sign_extend' 64 (mword_of_int 511 : mword 12)))
          (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)).
    { rewrite /L3 upd_eq /L2 upd_eq. reflexivity. }
    assert (H9a : L3 !!! Regidx (mword_of_int 9 : mword 5) = W9 !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /L3 /L2 /L1. do 3 (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HL4c : <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (add_vec (L3 !!! Regidx (mword_of_int 18 : mword 5)) (L3 !!! Regidx (mword_of_int 9 : mword 5)))]> L3 = L4).
    { rewrite H18a H9a. rewrite /L4 /L3 /L2 /L1 !upd_upd. do 2 f_equal.
      rewrite HW9s1; exact (walk_slot_addr2 (pt_base t) va Hva'). }
    iEval (rewrite HL4c) in "Hcg".
    assert (HL4s2 : L4 !!! Regidx (mword_of_int 18 : mword 5)
                    = u_pte_addr (pt_base t) (vpn_idx 2 vpn))
      by (rewrite /L4 upd_eq; reflexivity).
    assert (Hea0 : forall X : mword 64, add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* ---- +0x32 ld s1,0(s2): the slot read; pt_rep0 totality drives the branch ---- *)
    destruct (m !! vpn) as [w|] eqn:Hmv.
    - (* ============ MAPPED vpn: descend, descend ============ *)
      destruct (proj1 Hrep vpn w Hmv) as (p2 & p1 & Hmaps).
      pose proof Hmaps as (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hch2 & Hch1 &
                           Hv2 & Hp2c & Hv1 & Hp1c & Hv0 & Hl0c & Hnap0 & Hpb0).
      iDestruct (ptree_own_slot2_ro (DfracOwn 1) t vpn with "Hptree") as "[Hslot Hcl2]".
      iApply (wp_ld_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
                L4 (K - 8)%nat (pt_ents t (vpn_idx 2 vpn)) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi32 [Hslot] [-]").
      { iEval (rewrite Hea0 HL4s2). iExact "Hslot". }
      iIntros "Hhs Hsc Hcg Htlbinv Hpc Hslot".
      iEval (rewrite Hea0 HL4s2) in "Hslot".
      iDestruct ("Hcl2" with "Hslot") as "Hptree".
      set (L5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents t (vpn_idx 2 vpn))]> L4).
      assert (Hpp36 : add_vec_int (mword_of_int (WK + 0x32) : mword 64) 4 = mword_of_int (WK + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      (* +0x36 andi a5,s1,1 *)
      iApply (wp_andi_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
                (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                L5 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite /L5 upd_eq; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi36 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (L6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> L5).
      assert (Hpp3a : add_vec_int (mword_of_int (WK + 0x36) : mword 64) 4 = mword_of_int (WK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.beqz a5 FALLS: V = 1 *)
      assert (Hvbit2 : Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0 = true).
      { destruct (Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0) eqn:E;
          [reflexivity | exfalso].
        apply (pte_valid_invalid_excl (pt_ents t (vpn_idx 2 vpn))).
        - rewrite He2. exact Hv2.
        - exact (pte_invalid_bit0 _ E). }
      assert (HL6a5 : L6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /L6 upd_eq; reflexivity).
      iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                L6 (K - 8)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HL6a5 walk_vbit_eq Hvbit2; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3a [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Hpp3c : add_vec_int (mword_of_int (WK + 0x3a) : mword 64) 2 = mword_of_int (WK + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      iPoseProof (wi_3c with "Htext") as "Hi3c".
      iPoseProof (wi_3e with "Htext") as "Hi3e".
      iPoseProof (wi_40 with "Htext") as "Hi40".
      iPoseProof (wi_42 with "Htext") as "Hi42".
      assert (HL6s1 : L6 !!! Regidx (mword_of_int 9 : mword 5) = pt_ents t (vpn_idx 2 vpn)).
      { rewrite /L6. rewrite upd_ne; [| reg_neq].
        rewrite /L5 upd_eq. reflexivity. }
      (* +0x3c c.srli s1,10 *)
      iApply (wp_csrli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3c)) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
                L6 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3c [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (L7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_right (L6 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> L6).
      assert (Hpp3e : add_vec_int (mword_of_int (WK + 0x3c) : mword 64) 2 = mword_of_int (WK + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      (* +0x3e c.slli s1,12 *)
      iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3e)) (Regidx (mword_of_int 9 : mword 5)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
                L7 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3e [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (L8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_left (L7 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> L7).
      assert (Hpp40 : add_vec_int (mword_of_int (WK + 0x3e) : mword 64) 2 = mword_of_int (WK + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      assert (Hb1c : u_next_base (pt_ents t (vpn_idx 2 vpn)) = pt_base c1)
        by (rewrite He2; exact Hch2).
      assert (HL8s1 : L8 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /L8 upd_eq /L7 upd_eq HL6s1.
        rewrite (walk_descend_base (pt_ents t (vpn_idx 2 vpn))
                   ltac:(rewrite He2; exact Hv2) ltac:(rewrite He2; exact Hp2c)).
        rewrite Hb1c. reflexivity. }
      (* +0x40 c.addiw s4,-9 : 30 -> 21 *)
      iApply (wp_caddiw_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                L8 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi40 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (L9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (L8 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> L8).
      assert (Hpp42 : add_vec_int (mword_of_int (WK + 0x40) : mword 64) 2 = mword_of_int (WK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HL8s4 : L8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
      { rewrite /L8 /L7 /L6 /L5 /L4 /W9.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s4 : L9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /L9 upd_eq. rewrite HL8s4. apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s5 : L9 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
      (* +0x42 bne s4,s5 TAKEN (21 <> 12): back to +0x26 *)
      iApply (wp_bne_taken_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                L9 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HL9s4 HL9s5; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi42 [-]").
      iNext. iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Hbk26 : add_vec (mword_of_int (WK + 0x42) : mword 64) (sign_extend' 64 (mword_of_int 8164 : mword 13)) = mword_of_int (WK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbk26) in "Hpc".
      (* ================= LOOP ITERATION 2 (s4 = 21, level 1) ============ *)
      assert (HL9s3 : L9 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite add_vec_zero_l. reflexivity. }
      assert (HL9s1 : L9 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /L9. rewrite upd_ne; [| reg_neq]. exact HL8s1. }
      iDestruct (ptree_own_slot1_ro (DfracOwn 1) t c1 vpn Hk2 Hb1c with "Hptree") as "[Hslot1 Hcl1]".
      iEval (rewrite /pt_addr1 Hb1c) in "Hslot1".
      iApply (wp_walk_probe_sconf γ root_ppn Φ L9 (K - 8)%nat va (mword_of_int 21 : mword 64)
                (u_pte_addr (pt_base c1) (vpn_idx 1 vpn)) (pt_ents c1 (vpn_idx 1 vpn))
                (dqm:=DfracOwn 1)
                HL9s3 HL9s4
                ltac:(rewrite HL9s1; exact (walk_slot_addr1 (pt_base c1) va Hva'))
                with "Hsc Hhs Hcg Htlbinv Htext Hpc Hslot1 [-]").
      iIntros "Hsc Hhs Hcg Htlbinv Hpc Hslot1".
      set (M4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (u_pte_addr (pt_base c1) (vpn_idx 1 vpn))]> L9).
      set (M5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents c1 (vpn_idx 1 vpn))]> M4).
      set (M6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> M5).
      assert (HM4s2 : M4 !!! Regidx (mword_of_int 18 : mword 5)
                      = u_pte_addr (pt_base c1) (vpn_idx 1 vpn))
        by (rewrite /M4 upd_eq; reflexivity).
      iEval (rewrite /pt_addr1 Hb1c) in "Hcl1".
      iDestruct ("Hcl1" with "Hslot1") as "Hptree".
      (* +0x3a c.beqz a5 FALLS: mapped L1 slot V = 1 *)
      assert (Hvbit1 : Z.testbit (bv_unsigned (pt_ents c1 (vpn_idx 1 vpn))) 0 = true).
      { destruct (Z.testbit (bv_unsigned (pt_ents c1 (vpn_idx 1 vpn))) 0) eqn:E;
          [reflexivity | exfalso].
        apply (pte_valid_invalid_excl (pt_ents c1 (vpn_idx 1 vpn))).
        - rewrite He1. exact Hv1.
        - exact (pte_invalid_bit0 _ E). }
      assert (HM6a5 : M6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /M6 upd_eq; reflexivity).
      iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                M6 (K - 8)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HM6a5 walk_vbit_eq Hvbit1; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3a [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      iEval (rewrite Hpp3c) in "Hpc".
      assert (HM6s1 : M6 !!! Regidx (mword_of_int 9 : mword 5) = pt_ents c1 (vpn_idx 1 vpn)).
      { rewrite /M6. rewrite upd_ne; [| reg_neq].
        rewrite /M5 upd_eq. reflexivity. }
      (* +0x3c c.srli s1,10 *)
      iApply (wp_csrli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3c)) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
                M6 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3c [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (M7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_right (M6 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> M6).
      iEval (rewrite Hpp3e) in "Hpc".
      (* +0x3e c.slli s1,12 *)
      iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3e)) (Regidx (mword_of_int 9 : mword 5)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
                M7 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3e [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (M8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_left (M7 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> M7).
      iEval (rewrite Hpp40) in "Hpc".
      assert (Hb0c : u_next_base (pt_ents c1 (vpn_idx 1 vpn)) = pt_base c0)
        by (rewrite He1; exact Hch1).
      assert (HM8s1 : M8 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c0) (zeros' 12 : mword 12))).
      { rewrite /M8 upd_eq /M7 upd_eq HM6s1.
        rewrite (walk_descend_base (pt_ents c1 (vpn_idx 1 vpn))
                   ltac:(rewrite He1; exact Hv1) ltac:(rewrite He1; exact Hp1c)).
        rewrite Hb0c. reflexivity. }
      (* +0x40 c.addiw s4,-9 : 21 -> 12; +0x42 bne FALLS *)
      iApply (wp_caddiw_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                M8 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi40 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (M9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (M8 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> M8).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HM8s4 : M8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /M8 /M7 /M6 /M5 /M4.
        repeat (rewrite upd_ne; [| reg_neq]).
        exact HL9s4. }
      assert (HM9s4 : M9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /M9 upd_eq. rewrite HM8s4. apply bv_eq; vm_compute; reflexivity. }
      assert (HM9s5 : M9 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_bne_fall_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                M9 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HM9s4 HM9s5; vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi42 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Hpp46 : add_vec_int (mword_of_int (WK + 0x42) : mword 64) 4 = mword_of_int (WK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* ---- funnel into the shared tail with b0 := pt_base c0 ---- *)
      assert (HspM9 : M9 !!! Regidx csp_rs1 = spr).
      { peel_reg. }
      assert (HM9s3 : M9 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite add_vec_zero_l. reflexivity. }
      assert (HM9s1 : M9 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c0) (zeros' 12 : mword 12))).
      { rewrite /M9. rewrite upd_ne; [| reg_neq]. exact HM8s1. }
      assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r1) in "Hc56".
      assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r8) in "Hc48".
      assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r9) in "Hc40".
      assert (HW1r18 : W1 !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r18) in "Hc32".
      assert (HW1r19 : W1 !!! Regidx (mword_of_int 19 : mword 5) = mm !!! Regidx (mword_of_int 19)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r19) in "Hc24".
      assert (HW1r20 : W1 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 20)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r20) in "Hc16".
      assert (HW1r21 : W1 !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 21)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r21) in "Hc08".
      assert (HW1r22 : W1 !!! Regidx (mword_of_int 22 : mword 5) = mm !!! Regidx (mword_of_int 22)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r22) in "Hc00".
      iEval (rewrite HspW1 Hb1) in "Hc56".
      iEval (rewrite HspW1 Hb2) in "Hc48".
      iEval (rewrite HspW1 Hb3) in "Hc40".
      iEval (rewrite HspW1 Hb4) in "Hc32".
      iEval (rewrite HspW1 Hb5) in "Hc24".
      iEval (rewrite HspW1 Hb6) in "Hc16".
      iEval (rewrite HspW1 Hb7) in "Hc08".
      iEval (rewrite HspW1 Hb8) in "Hc00".
      unshelve iApply (wp_walk_tail_sconf γ root_ppn γa Φ mm M9 t t (pt_base c0) K lvl HK Hva'
                HspM9 HM9s3 HM9s1
                _ _ _ _ _ _
                (ptree_same_rep0_refl t)
                _
                with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hptree Henv Hcont").
      all: first
        [ peel_reg
        | (exists p2, p1, w; split;
           [exact (ptree_maps_level0 t vpn p2 p1 w Hmaps)
           | unfold pt_addr0; rewrite Hch1; reflexivity]) ].
    - (* ============ UNMAPPED vpn: the blocks0 dichotomy ============ *)
      pose proof (proj2 Hrep vpn Hmv) as Hblk.
      destruct Hblk as [ (Hk2n & He2z)
                       | [ (c1 & Hk2 & Hk1 & Hv2 & Hp2c & Hch2 & He1z)
                         | (c1 & c0 & Hk2 & Hk1 & Hv2 & Hp2c & Hv1 & Hp1c & Hch2 & Hch1 & He0z) ] ].
      3:{ (* ---- arm 3: descend, descend, zero L0 word ---- *)
      iDestruct (ptree_own_slot2_ro (DfracOwn 1) t vpn with "Hptree") as "[Hslot Hcl2]".
      iApply (wp_ld_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
                L4 (K - 8)%nat (pt_ents t (vpn_idx 2 vpn)) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi32 [Hslot] [-]").
      { iEval (rewrite Hea0 HL4s2). iExact "Hslot". }
      iIntros "Hhs Hsc Hcg Htlbinv Hpc Hslot".
      iEval (rewrite Hea0 HL4s2) in "Hslot".
      iDestruct ("Hcl2" with "Hslot") as "Hptree".
      set (L5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents t (vpn_idx 2 vpn))]> L4).
      assert (Hpp36 : add_vec_int (mword_of_int (WK + 0x32) : mword 64) 4 = mword_of_int (WK + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      iApply (wp_andi_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
                (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                L5 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite /L5 upd_eq; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi36 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (L6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> L5).
      assert (Hpp3a : add_vec_int (mword_of_int (WK + 0x36) : mword 64) 4 = mword_of_int (WK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      assert (Hvbit2 : Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0 = true).
      { destruct (Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0) eqn:E;
          [reflexivity | exfalso].
        apply (pte_valid_invalid_excl (pt_ents t (vpn_idx 2 vpn))).
        - exact Hv2.
        - exact (pte_invalid_bit0 _ E). }
      assert (HL6a5 : L6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /L6 upd_eq; reflexivity).
      iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                L6 (K - 8)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HL6a5 walk_vbit_eq Hvbit2; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3a [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Hpp3c : add_vec_int (mword_of_int (WK + 0x3a) : mword 64) 2 = mword_of_int (WK + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      iPoseProof (wi_3c with "Htext") as "Hi3c".
      iPoseProof (wi_3e with "Htext") as "Hi3e".
      iPoseProof (wi_40 with "Htext") as "Hi40".
      iPoseProof (wi_42 with "Htext") as "Hi42".
      assert (HL6s1 : L6 !!! Regidx (mword_of_int 9 : mword 5) = pt_ents t (vpn_idx 2 vpn)).
      { rewrite /L6. rewrite upd_ne; [| reg_neq].
        rewrite /L5 upd_eq. reflexivity. }
      iApply (wp_csrli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3c)) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
                L6 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3c [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (L7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_right (L6 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> L6).
      assert (Hpp3e : add_vec_int (mword_of_int (WK + 0x3c) : mword 64) 2 = mword_of_int (WK + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3e)) (Regidx (mword_of_int 9 : mword 5)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
                L7 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3e [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (L8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_left (L7 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> L7).
      assert (Hpp40 : add_vec_int (mword_of_int (WK + 0x3e) : mword 64) 2 = mword_of_int (WK + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      pose proof Hch2 as Hb1c.
      assert (HL8s1 : L8 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /L8 upd_eq /L7 upd_eq HL6s1.
        rewrite (walk_descend_base (pt_ents t (vpn_idx 2 vpn)) Hv2 Hp2c).
        rewrite Hb1c. reflexivity. }
      iApply (wp_caddiw_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                L8 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi40 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (L9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (L8 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> L8).
      assert (Hpp42 : add_vec_int (mword_of_int (WK + 0x40) : mword 64) 2 = mword_of_int (WK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HL8s4 : L8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
      { rewrite /L8 /L7 /L6 /L5 /L4 /W9.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s4 : L9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /L9 upd_eq. rewrite HL8s4. apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s5 : L9 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_bne_taken_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                L9 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HL9s4 HL9s5; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi42 [-]").
      iNext. iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Hbk26 : add_vec (mword_of_int (WK + 0x42) : mword 64) (sign_extend' 64 (mword_of_int 8164 : mword 13)) = mword_of_int (WK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbk26) in "Hpc".
      assert (HL9s3 : L9 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite add_vec_zero_l. reflexivity. }
      assert (HL9s1 : L9 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /L9. rewrite upd_ne; [| reg_neq]. exact HL8s1. }
      iDestruct (ptree_own_slot1_ro (DfracOwn 1) t c1 vpn Hk2 Hb1c with "Hptree") as "[Hslot1 Hcl1]".
      iEval (rewrite /pt_addr1 Hb1c) in "Hslot1".
      iApply (wp_walk_probe_sconf γ root_ppn Φ L9 (K - 8)%nat va (mword_of_int 21 : mword 64)
                (u_pte_addr (pt_base c1) (vpn_idx 1 vpn)) (pt_ents c1 (vpn_idx 1 vpn))
                (dqm:=DfracOwn 1)
                HL9s3 HL9s4
                ltac:(rewrite HL9s1; exact (walk_slot_addr1 (pt_base c1) va Hva'))
                with "Hsc Hhs Hcg Htlbinv Htext Hpc Hslot1 [-]").
      iIntros "Hsc Hhs Hcg Htlbinv Hpc Hslot1".
      set (M4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (u_pte_addr (pt_base c1) (vpn_idx 1 vpn))]> L9).
      set (M5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents c1 (vpn_idx 1 vpn))]> M4).
      set (M6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> M5).
      assert (HM4s2 : M4 !!! Regidx (mword_of_int 18 : mword 5)
                      = u_pte_addr (pt_base c1) (vpn_idx 1 vpn))
        by (rewrite /M4 upd_eq; reflexivity).
      iEval (rewrite /pt_addr1 Hb1c) in "Hcl1".
      iDestruct ("Hcl1" with "Hslot1") as "Hptree".
      assert (Hvbit1 : Z.testbit (bv_unsigned (pt_ents c1 (vpn_idx 1 vpn))) 0 = true).
      { destruct (Z.testbit (bv_unsigned (pt_ents c1 (vpn_idx 1 vpn))) 0) eqn:E;
          [reflexivity | exfalso].
        apply (pte_valid_invalid_excl (pt_ents c1 (vpn_idx 1 vpn))).
        - exact Hv1.
        - exact (pte_invalid_bit0 _ E). }
      assert (HM6a5 : M6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /M6 upd_eq; reflexivity).
      iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                M6 (K - 8)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HM6a5 walk_vbit_eq Hvbit1; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3a [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      iEval (rewrite Hpp3c) in "Hpc".
      assert (HM6s1 : M6 !!! Regidx (mword_of_int 9 : mword 5) = pt_ents c1 (vpn_idx 1 vpn)).
      { rewrite /M6. rewrite upd_ne; [| reg_neq].
        rewrite /M5 upd_eq. reflexivity. }
      iApply (wp_csrli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3c)) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
                M6 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3c [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (M7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_right (M6 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> M6).
      iEval (rewrite Hpp3e) in "Hpc".
      iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3e)) (Regidx (mword_of_int 9 : mword 5)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
                M7 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3e [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (M8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_left (M7 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> M7).
      iEval (rewrite Hpp40) in "Hpc".
      pose proof Hch1 as Hb0c.
      assert (HM8s1 : M8 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c0) (zeros' 12 : mword 12))).
      { rewrite /M8 upd_eq /M7 upd_eq HM6s1.
        rewrite (walk_descend_base (pt_ents c1 (vpn_idx 1 vpn)) Hv1 Hp1c).
        rewrite Hb0c. reflexivity. }
      iApply (wp_caddiw_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                M8 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi40 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (M9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (M8 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> M8).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HM8s4 : M8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /M8 /M7 /M6 /M5 /M4.
        repeat (rewrite upd_ne; [| reg_neq]).
        exact HL9s4. }
      assert (HM9s4 : M9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /M9 upd_eq. rewrite HM8s4. apply bv_eq; vm_compute; reflexivity. }
      assert (HM9s5 : M9 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_bne_fall_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                M9 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HM9s4 HM9s5; vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi42 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Hpp46 : add_vec_int (mword_of_int (WK + 0x42) : mword 64) 4 = mword_of_int (WK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      assert (HspM9 : M9 !!! Regidx csp_rs1 = spr).
      { peel_reg. }
      assert (HM9s3 : M9 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite add_vec_zero_l. reflexivity. }
      assert (HM9s1 : M9 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c0) (zeros' 12 : mword 12))).
      { rewrite /M9. rewrite upd_ne; [| reg_neq]. exact HM8s1. }
      assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r1) in "Hc56".
      assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r8) in "Hc48".
      assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r9) in "Hc40".
      assert (HW1r18 : W1 !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r18) in "Hc32".
      assert (HW1r19 : W1 !!! Regidx (mword_of_int 19 : mword 5) = mm !!! Regidx (mword_of_int 19)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r19) in "Hc24".
      assert (HW1r20 : W1 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 20)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r20) in "Hc16".
      assert (HW1r21 : W1 !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 21)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r21) in "Hc08".
      assert (HW1r22 : W1 !!! Regidx (mword_of_int 22 : mword 5) = mm !!! Regidx (mword_of_int 22)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r22) in "Hc00".
      iEval (rewrite HspW1 Hb1) in "Hc56".
      iEval (rewrite HspW1 Hb2) in "Hc48".
      iEval (rewrite HspW1 Hb3) in "Hc40".
      iEval (rewrite HspW1 Hb4) in "Hc32".
      iEval (rewrite HspW1 Hb5) in "Hc24".
      iEval (rewrite HspW1 Hb6) in "Hc16".
      iEval (rewrite HspW1 Hb7) in "Hc08".
      iEval (rewrite HspW1 Hb8) in "Hc00".
      unshelve iApply (wp_walk_tail_sconf γ root_ppn γa Φ mm M9 t t (pt_base c0) K lvl HK Hva'
                HspM9 HM9s3 HM9s1
                _ _ _ _ _ _
                (ptree_same_rep0_refl t)
                _
                with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hptree Henv Hcont").
      all: first
        [ peel_reg
        | (pose proof (ptree_level0_intro t c1 c0 vpn Hk2 Hk1 Hv2 Hp2c Hv1 Hp1c Hch2 Hch1) as Hl0;
           rewrite He0z in Hl0;
           eexists _, _, _; split;
           [exact Hl0 | unfold pt_addr0; rewrite Hch1; reflexivity]) ].
      }
      2:{ (* ---- arm 2: descend, then ALLOCATE at level 1 ---- *)
      iDestruct (ptree_own_slot2_ro (DfracOwn 1) t vpn with "Hptree") as "[Hslot Hcl2]".
      iApply (wp_ld_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
                L4 (K - 8)%nat (pt_ents t (vpn_idx 2 vpn)) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi32 [Hslot] [-]").
      { iEval (rewrite Hea0 HL4s2). iExact "Hslot". }
      iIntros "Hhs Hsc Hcg Htlbinv Hpc Hslot".
      iEval (rewrite Hea0 HL4s2) in "Hslot".
      iDestruct ("Hcl2" with "Hslot") as "Hptree".
      set (L5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents t (vpn_idx 2 vpn))]> L4).
      assert (Hpp36 : add_vec_int (mword_of_int (WK + 0x32) : mword 64) 4 = mword_of_int (WK + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      iApply (wp_andi_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
                (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                L5 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite /L5 upd_eq; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi36 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (L6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> L5).
      assert (Hpp3a : add_vec_int (mword_of_int (WK + 0x36) : mword 64) 4 = mword_of_int (WK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      assert (Hvbit2 : Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0 = true).
      { destruct (Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0) eqn:E;
          [reflexivity | exfalso].
        apply (pte_valid_invalid_excl (pt_ents t (vpn_idx 2 vpn))).
        - exact Hv2.
        - exact (pte_invalid_bit0 _ E). }
      assert (HL6a5 : L6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /L6 upd_eq; reflexivity).
      iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                L6 (K - 8)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HL6a5 walk_vbit_eq Hvbit2; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3a [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Hpp3c : add_vec_int (mword_of_int (WK + 0x3a) : mword 64) 2 = mword_of_int (WK + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      iPoseProof (wi_3c with "Htext") as "Hi3c".
      iPoseProof (wi_3e with "Htext") as "Hi3e".
      iPoseProof (wi_40 with "Htext") as "Hi40".
      iPoseProof (wi_42 with "Htext") as "Hi42".
      assert (HL6s1 : L6 !!! Regidx (mword_of_int 9 : mword 5) = pt_ents t (vpn_idx 2 vpn)).
      { rewrite /L6. rewrite upd_ne; [| reg_neq].
        rewrite /L5 upd_eq. reflexivity. }
      iApply (wp_csrli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3c)) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
                L6 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3c [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (L7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_right (L6 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> L6).
      assert (Hpp3e : add_vec_int (mword_of_int (WK + 0x3c) : mword 64) 2 = mword_of_int (WK + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3e)) (Regidx (mword_of_int 9 : mword 5)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
                L7 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3e [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (L8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_left (L7 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> L7).
      assert (Hpp40 : add_vec_int (mword_of_int (WK + 0x3e) : mword 64) 2 = mword_of_int (WK + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      pose proof Hch2 as Hb1c.
      assert (HL8s1 : L8 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /L8 upd_eq /L7 upd_eq HL6s1.
        rewrite (walk_descend_base (pt_ents t (vpn_idx 2 vpn)) Hv2 Hp2c).
        rewrite Hb1c. reflexivity. }
      iApply (wp_caddiw_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                L8 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi40 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (L9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (L8 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> L8).
      assert (Hpp42 : add_vec_int (mword_of_int (WK + 0x40) : mword 64) 2 = mword_of_int (WK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HL8s4 : L8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
      { rewrite /L8 /L7 /L6 /L5 /L4 /W9.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s4 : L9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /L9 upd_eq. rewrite HL8s4. apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s5 : L9 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_bne_taken_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                L9 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HL9s4 HL9s5; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi42 [-]").
      iNext. iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Hbk26 : add_vec (mword_of_int (WK + 0x42) : mword 64) (sign_extend' 64 (mword_of_int 8164 : mword 13)) = mword_of_int (WK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbk26) in "Hpc".
      assert (HL9s3 : L9 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite add_vec_zero_l. reflexivity. }
      assert (HL9s1 : L9 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /L9. rewrite upd_ne; [| reg_neq]. exact HL8s1. }
      iDestruct (ptree_own_slot1_ro (DfracOwn 1) t c1 vpn Hk2 Hb1c with "Hptree") as "[Hslot1 Hcl1]".
      iEval (rewrite /pt_addr1 Hb1c) in "Hslot1".
      iApply (wp_walk_probe_sconf γ root_ppn Φ L9 (K - 8)%nat va (mword_of_int 21 : mword 64)
                (u_pte_addr (pt_base c1) (vpn_idx 1 vpn)) (pt_ents c1 (vpn_idx 1 vpn))
                (dqm:=DfracOwn 1)
                HL9s3 HL9s4
                ltac:(rewrite HL9s1; exact (walk_slot_addr1 (pt_base c1) va Hva'))
                with "Hsc Hhs Hcg Htlbinv Htext Hpc Hslot1 [-]").
      iIntros "Hsc Hhs Hcg Htlbinv Hpc Hslot1".
      set (M4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (u_pte_addr (pt_base c1) (vpn_idx 1 vpn))]> L9).
      set (M5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents c1 (vpn_idx 1 vpn))]> M4).
      set (M6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> M5).
      assert (HM4s2 : M4 !!! Regidx (mword_of_int 18 : mword 5)
                      = u_pte_addr (pt_base c1) (vpn_idx 1 vpn))
        by (rewrite /M4 upd_eq; reflexivity).
      iEval (rewrite /pt_addr1 Hb1c) in "Hcl1".
      iDestruct ("Hcl1" with "Hslot1") as "Hptree".
      (* +0x3a c.beqz a5 TAKEN: the L1 slot is the ZERO stop word *)
      assert (Hvbit0 : Z.testbit (bv_unsigned (pt_ents c1 (vpn_idx 1 vpn))) 0 = false).
      { rewrite He1z.
        replace (bv_unsigned (mword_of_int 0 : mword 64)) with 0 by (vm_compute; reflexivity).
        apply Z.bits_0. }
      assert (HM6a5 : M6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /M6 upd_eq; reflexivity).
      iApply (wp_cbeqz_taken_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                M6 (K - 8)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HM6a5 walk_vbit_eq Hvbit0; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3a [-]").
      iNext. iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Htgt72 : add_vec (mword_of_int (WK + 0x3a) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0"))))
              = mword_of_int (WK + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt72) in "Hpc".
      assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r1 HspW1 Hb1) in "Hc56".
      assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r8 HspW1 Hb2) in "Hc48".
      assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r9 HspW1 Hb3) in "Hc40".
      assert (HW1r18 : W1 !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r18 HspW1 Hb4) in "Hc32".
      assert (HW1r19 : W1 !!! Regidx (mword_of_int 19 : mword 5) = mm !!! Regidx (mword_of_int 19)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r19 HspW1 Hb5) in "Hc24".
      assert (HW1r20 : W1 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 20)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r20 HspW1 Hb6) in "Hc16".
      assert (HW1r21 : W1 !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 21)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r21 HspW1 Hb7) in "Hc08".
      assert (HW1r22 : W1 !!! Regidx (mword_of_int 22 : mword 5) = mm !!! Regidx (mword_of_int 22)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r22 HspW1 Hb8) in "Hc00".
      pose proof (ptree_own_graft1 (DfracOwn 1) t c1 vpn Hk2 Hk1 Hb1c) as Hacc2.
      unfold pt_addr1 in Hacc2. rewrite Hb1c in Hacc2.
      iApply (wp_walk_alloc_sconf γ root_ppn γa Φ mm M6 t t
                (fun b => pt_graft1 t vpn b) 0
                (u_pte_addr (pt_base c1) (vpn_idx 1 vpn))
                (pt_ents c1 (vpn_idx 1 vpn)) K lvl Hlvl HK
                ltac:(peel_reg)
                ltac:(rewrite /M6 /M5;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      exact HM4s2)
                ltac:(rewrite /M6 /M5 /M4 /L9 /L8 /L7 /L6;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite upd_eq;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite Ha2 add_vec_zero_l; vm_compute; reflexivity)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                (ptree_same_rep0_refl t) Hacc2
                with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hptree Henv [Hi40 Hi42] Hcont").
      iIntros (Mo b) "%Htrans %Hs1b Hsc Hhs Hcg Hcnt Htlbinv Hpc
               Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hptree Henv Hcont".
      assert (HMos4 : Mo !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite (Htrans (mword_of_int 20) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /M6 /M5 /M4.
        repeat (rewrite upd_ne; [| reg_neq]).
        exact HL9s4. }
      assert (HMos5 : Mo !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite (Htrans (mword_of_int 21) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /M6 /M5 /M4 /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_caddiw_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                Mo (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi40 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (G1 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (Mo !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> Mo).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HG1s4 : G1 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /G1 upd_eq. rewrite HMos4. apply bv_eq; vm_compute; reflexivity. }
      assert (HG1s5 : G1 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /G1. rewrite upd_ne; [| reg_neq]. exact HMos5. }
      iApply (wp_bne_fall_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                G1 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HG1s4 HG1s5; vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi42 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Hpp46 : add_vec_int (mword_of_int (WK + 0x42) : mword 64) 4 = mword_of_int (WK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      iApply (wp_walk_tail_sconf γ root_ppn γa Φ mm G1 t (pt_graft1 t vpn b) b K lvl HK Hva'
                ltac:(rewrite /G1; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans csp_rs1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G1; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 19) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /M6 /M5 /M4;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite upd_eq;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite add_vec_zero_l; reflexivity)
                ltac:(rewrite /G1; rewrite upd_ne; [| reg_neq];
                      exact Hs1b)
                ltac:(rewrite /G1; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 4) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G1; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G1; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G1; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G1; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G1; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                (pt_graft1_same_rep0 t c1 vpn b Hk2 Hk1 He1z)
                ltac:(pose proof (pt_graft1_level0 t c1 vpn b Hk2
                        ltac:(exact Hv2) ltac:(exact Hp2c) Hb1c) as Hl0;
                      eexists _, _, _; split;
                      [exact Hl0
                      | unfold pt_addr0; rewrite pt_ptr_pte_base; reflexivity])
                with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hptree Henv Hcont").
      }
      (* ---- arm 1: ZERO ROOT slot: allocate at L2, loop, allocate at L1 ---- *)
      iPoseProof (wi_40 with "Htext") as "Hi40".
      iPoseProof (wi_42 with "Htext") as "Hi42".
      iDestruct (ptree_own_slot2_ro (DfracOwn 1) t vpn with "Hptree") as "[Hslot Hcl2]".
      iApply (wp_ld_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
                L4 (K - 8)%nat (pt_ents t (vpn_idx 2 vpn)) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi32 [Hslot] [-]").
      { iEval (rewrite Hea0 HL4s2). iExact "Hslot". }
      iIntros "Hhs Hsc Hcg Htlbinv Hpc Hslot".
      iEval (rewrite Hea0 HL4s2) in "Hslot".
      iDestruct ("Hcl2" with "Hslot") as "Hptree".
      set (L5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents t (vpn_idx 2 vpn))]> L4).
      assert (Hpp36 : add_vec_int (mword_of_int (WK + 0x32) : mword 64) 4 = mword_of_int (WK + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      iApply (wp_andi_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
                (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                L5 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite /L5 upd_eq; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi36 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (L6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> L5).
      assert (Hpp3a : add_vec_int (mword_of_int (WK + 0x36) : mword 64) 4 = mword_of_int (WK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      assert (Hvbit0 : Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0 = false).
      { rewrite He2z.
        replace (bv_unsigned (mword_of_int 0 : mword 64)) with 0 by (vm_compute; reflexivity).
        apply Z.bits_0. }
      assert (HL6a5 : L6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /L6 upd_eq; reflexivity).
      iApply (wp_cbeqz_taken_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                L6 (K - 8)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HL6a5 walk_vbit_eq Hvbit0; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3a [-]").
      iNext. iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Htgt72 : add_vec (mword_of_int (WK + 0x3a) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0"))))
              = mword_of_int (WK + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt72) in "Hpc".
      assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r1 HspW1 Hb1) in "Hc56".
      assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r8 HspW1 Hb2) in "Hc48".
      assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r9 HspW1 Hb3) in "Hc40".
      assert (HW1r18 : W1 !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r18 HspW1 Hb4) in "Hc32".
      assert (HW1r19 : W1 !!! Regidx (mword_of_int 19 : mword 5) = mm !!! Regidx (mword_of_int 19)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r19 HspW1 Hb5) in "Hc24".
      assert (HW1r20 : W1 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 20)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r20 HspW1 Hb6) in "Hc16".
      assert (HW1r21 : W1 !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 21)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r21 HspW1 Hb7) in "Hc08".
      assert (HW1r22 : W1 !!! Regidx (mword_of_int 22 : mword 5) = mm !!! Regidx (mword_of_int 22)).
      { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r22 HspW1 Hb8) in "Hc00".
      pose proof (ptree_own_graft2 (DfracOwn 1) t vpn Hk2n) as Hacc1.
      unfold pt_addr2 in Hacc1.
      iApply (wp_walk_alloc_sconf γ root_ppn γa Φ mm L6 t t
                (fun b => pt_graft2 t vpn b) 1
                (u_pte_addr (pt_base t) (vpn_idx 2 vpn))
                (pt_ents t (vpn_idx 2 vpn)) K lvl Hlvl HK
                ltac:(peel_reg)
                ltac:(rewrite /L6 /L5;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      exact HL4s2)
                ltac:(rewrite /L6 /L5 /L4;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite upd_eq;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite Ha2 add_vec_zero_l; vm_compute; reflexivity)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                (ptree_same_rep0_refl t) Hacc1
                with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hptree Henv [Hi40 Hi42] Hcont").
      iIntros (Mo1 b1) "%Htrans1 %Hs1b1 Hsc Hhs Hcg Hcnt Htlbinv Hpc
               Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hptree Henv Hcont".
      assert (HMo1s4 : Mo1 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
      { rewrite (Htrans1 (mword_of_int 20) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /L6 /L5.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
      assert (HMo1s5 : Mo1 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite (Htrans1 (mword_of_int 21) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /L6 /L5 /L4.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_caddiw_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                Mo1 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi40 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (G1 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (Mo1 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> Mo1).
      assert (Hpp42 : add_vec_int (mword_of_int (WK + 0x40) : mword 64) 2 = mword_of_int (WK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HG1s4 : G1 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /G1 upd_eq. rewrite HMo1s4. apply bv_eq; vm_compute; reflexivity. }
      assert (HG1s5 : G1 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /G1. rewrite upd_ne; [| reg_neq]. exact HMo1s5. }
      iApply (wp_bne_taken_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                G1 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HG1s4 HG1s5; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi42 [-]").
      iNext. iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Hbk26 : add_vec (mword_of_int (WK + 0x42) : mword 64) (sign_extend' 64 (mword_of_int 8164 : mword 13)) = mword_of_int (WK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbk26) in "Hpc".
      (* ===== LOOP ITERATION 2 on the grafted tree (s4 = 21, level 1) ===== *)
      assert (HG1s3 : G1 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /G1. rewrite upd_ne; [| reg_neq].
        rewrite (Htrans1 (mword_of_int 19) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /L6 /L5 /L4.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite add_vec_zero_l. reflexivity. }
      iApply (wp_srl_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x26)) (mword_of_int 18 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 20 : mword 5)
                (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
                G1 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HG1s3 HG1s4; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi26 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (K1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))]> G1).
      iEval (rewrite Hpp2a) in "Hpc".
      iApply (wp_andi_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x2a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 511 : mword 12)
                (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
                         (sign_extend' 64 (mword_of_int 511 : mword 12)))
                K1 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite /K1 upd_eq; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi2a [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (K2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
                   (sign_extend' 64 (mword_of_int 511 : mword 12)))]> K1).
      iEval (rewrite Hpp2e) in "Hpc".
      iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x2e)) (Regidx (mword_of_int 18 : mword 5)) (mword_of_int 18 : mword 5) (mword_of_int 3 : mword 6)
                K2 (K - 8)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi2e [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (K3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (shift_bits_left (K2 !!! Regidx (mword_of_int 18 : mword 5)) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> K2).
      iEval (rewrite Hpp30) in "Hpc".
      iApply (wp_cadd_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x30)) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
                K3 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi30 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      iEval (rewrite Hpp32) in "Hpc".
      assert (HG1s1 : G1 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec b1 (zeros' 12 : mword 12))).
      { first [ exact Hs1b1
              | (rewrite /G1; repeat (rewrite upd_ne; [| reg_neq]); exact Hs1b1) ]. }
      set (K4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (u_pte_addr b1 (vpn_idx 1 vpn))]> G1).
      assert (HK18a : K3 !!! Regidx (mword_of_int 18 : mword 5) =
          shift_bits_left (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0)) (sign_extend' 64 (mword_of_int 511 : mword 12)))
            (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)).
      { rewrite /K3 upd_eq /K2 upd_eq. reflexivity. }
      assert (HK9a : K3 !!! Regidx (mword_of_int 9 : mword 5) = G1 !!! Regidx (mword_of_int 9 : mword 5)).
      { rewrite /K3 /K2 /K1. do 3 (rewrite upd_ne; [| reg_neq]). reflexivity. }
      assert (HK4c : <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (add_vec (K3 !!! Regidx (mword_of_int 18 : mword 5)) (K3 !!! Regidx (mword_of_int 9 : mword 5)))]> K3 = K4).
      { rewrite HK18a HK9a. rewrite /K4 /K3 /K2 /K1 !upd_upd. do 2 f_equal.
        rewrite HG1s1; exact (walk_slot_addr1 b1 va Hva'). }
      iEval (rewrite HK4c) in "Hcg".
      assert (HK4s2 : K4 !!! Regidx (mword_of_int 18 : mword 5)
                      = u_pte_addr b1 (vpn_idx 1 vpn))
        by (rewrite /K4 upd_eq; reflexivity).
      pose proof (pt_graft2_kid t vpn b1) as Hk2g.
      assert (Hb1cg : u_next_base (pt_ents (pt_graft2 t vpn b1) (vpn_idx 2 vpn)) = b1)
        by (rewrite pt_graft2_ent pt_ptr_pte_base; reflexivity).
      assert (Hch2g : u_next_base (pt_ents (pt_graft2 t vpn b1) (vpn_idx 2 vpn)) = pt_base (pt_empty_node b1))
        by (rewrite pt_graft2_ent pt_ptr_pte_base pt_empty_node_base; reflexivity).
      assert (He1zg : pt_ents (pt_empty_node b1) (vpn_idx 1 vpn) = mword_of_int 0) by reflexivity.
      iDestruct (ptree_own_slot1_ro (DfracOwn 1) (pt_graft2 t vpn b1) (pt_empty_node b1) vpn Hk2g Hch2g with "Hptree") as "[Hslot1 Hcl1]".
      iApply (wp_ld_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
                K4 (K - 8)%nat (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn)) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi32 [Hslot1] [-]").
      { iEval (rewrite Hea0 HK4s2). iEval (rewrite /pt_addr1 Hb1cg) in "Hslot1". iExact "Hslot1". }
      iIntros "Hhs Hsc Hcg Htlbinv Hpc Hslot1".
      iEval (rewrite Hea0 HK4s2) in "Hslot1".
      iEval (rewrite /pt_addr1 Hb1cg) in "Hcl1".
      iDestruct ("Hcl1" with "Hslot1") as "Hptree".
      set (K5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn))]> K4).
      iEval (rewrite Hpp36) in "Hpc".
      iApply (wp_andi_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
                (and_vec (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                K5 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite /K5 upd_eq; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi36 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (K6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> K5).
      iEval (rewrite Hpp3a) in "Hpc".
      assert (Hvbit0g : Z.testbit (bv_unsigned (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn))) 0 = false).
      { rewrite He1zg.
        replace (bv_unsigned (mword_of_int 0 : mword 64)) with 0 by (vm_compute; reflexivity).
        apply Z.bits_0. }
      assert (HK6a5 : K6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /K6 upd_eq; reflexivity).
      iApply (wp_cbeqz_taken_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                K6 (K - 8)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HK6a5 walk_vbit_eq Hvbit0g; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi3a [-]").
      iNext. iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      iEval (rewrite Htgt72) in "Hpc".
      pose proof (ptree_own_graft1 (DfracOwn 1) (pt_graft2 t vpn b1) (pt_empty_node b1) vpn Hk2g ltac:(reflexivity) Hch2g) as Hacc2.
      unfold pt_addr1 in Hacc2. rewrite Hb1cg in Hacc2.
      iApply (wp_walk_alloc_sconf γ root_ppn γa Φ mm K6 t (pt_graft2 t vpn b1)
                (fun b2 => pt_graft1 (pt_graft2 t vpn b1) vpn b2) 0
                (u_pte_addr b1 (vpn_idx 1 vpn))
                (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn)) K lvl Hlvl HK
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (csp_rs1) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /K6 /K5;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      exact HK4s2)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 22) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /L6 /L5 /L4;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite upd_eq;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite Ha2 add_vec_zero_l; vm_compute; reflexivity)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 4) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                (pt_graft2_same_rep0 t vpn b1 Hk2n He2z) Hacc2
                with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hptree Henv [Hi40 Hi42] Hcont").
      iIntros (Mo2 b2) "%Htrans2 %Hs1b2 Hsc Hhs Hcg Hcnt Htlbinv Hpc
               Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hptree Henv Hcont".
      assert (HMo2s4 : Mo2 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite (Htrans2 (mword_of_int 20) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /K6 /K5 /K4 /K3 /K2 /K1.
        repeat (rewrite upd_ne; [| reg_neq]).
        rewrite upd_eq. rewrite HMo1s4.
        apply bv_eq; vm_compute; reflexivity. }
      assert (HMo2s5 : Mo2 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite (Htrans2 (mword_of_int 21) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /K6 /K5 /K4 /K3 /K2 /K1.
        repeat (rewrite upd_ne; [| reg_neq]).
        exact HMo1s5. }
      iApply (wp_caddiw_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                Mo2 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi40 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      set (G2 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (Mo2 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> Mo2).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HG2s4 : G2 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /G2 upd_eq. rewrite HMo2s4. apply bv_eq; vm_compute; reflexivity. }
      assert (HG2s5 : G2 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /G2. rewrite upd_ne; [| reg_neq]. exact HMo2s5. }
      iApply (wp_bne_fall_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                G2 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HG2s4 HG2s5; vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hi42 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Hpp46 : add_vec_int (mword_of_int (WK + 0x42) : mword 64) 4 = mword_of_int (WK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      assert (Hv2g : pte_valid (pt_ents (pt_graft2 t vpn b1) (vpn_idx 2 vpn)))
        by (rewrite pt_graft2_ent; exact (pt_ptr_pte_valid b1)).
      assert (Hp2g : pte_ptr (pt_ents (pt_graft2 t vpn b1) (vpn_idx 2 vpn)))
        by (rewrite pt_graft2_ent; exact (pt_ptr_pte_ptr b1)).
      iApply (wp_walk_tail_sconf γ root_ppn γa Φ mm G2 t (pt_graft1 (pt_graft2 t vpn b1) vpn b2) b2 K lvl HK Hva'
                ltac:(rewrite /G2; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans2 (csp_rs1) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (csp_rs1) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G2; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 19) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 19) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /L6 /L5 /L4;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite upd_eq;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite add_vec_zero_l; reflexivity)
                ltac:(rewrite /G2; rewrite upd_ne; [| reg_neq];
                      exact Hs1b2)
                ltac:(rewrite /G2; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 4) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 4) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G2; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G2; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G2; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G2; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G2; rewrite upd_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite upd_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                (ptree_same_rep0_trans t (pt_graft2 t vpn b1) (pt_graft1 (pt_graft2 t vpn b1) vpn b2)
                   (pt_graft2_same_rep0 t vpn b1 Hk2n He2z)
                   (pt_graft1_same_rep0 (pt_graft2 t vpn b1) (pt_empty_node b1) vpn b2 Hk2g ltac:(reflexivity) ltac:(reflexivity)))
                ltac:(pose proof (pt_graft1_level0 (pt_graft2 t vpn b1) (pt_empty_node b1) vpn b2 Hk2g Hv2g Hp2g Hch2g) as Hl0;
                      eexists _, _, _; split;
                      [exact Hl0
                      | unfold pt_addr0; rewrite pt_ptr_pte_base; reflexivity])
                with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hptree Henv Hcont").
  Qed.

End WpSconfWalk.

End WalkProof.
