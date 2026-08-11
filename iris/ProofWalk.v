(* ProofWalk.v -- the whole-function WP for xv6's walk() over the
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
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import WpSconfVc.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv.
Require Import KMap.   (* mem_page_to_phys: kalloc-page ↦ₘ → ↦ₚ for the PT node *)
Require Import WpLock.
Require Import VcGen.
Require Import CommonWalk PtTree.
Require Import KptTree.   (* pt_slot_phys_to_mem / pt_slot_mem_to_phys / pt_node_claim_from_static *)
Require Import PtBuild KvmSpec.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecMemset.
Require Import SpecKalloc.
Require Import CodeWalk.
Require Import WpMemsetPage.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import SpecWalk.
Require Import KernelRvcDecode.
Import Defs.
Local Open Scope Z_scope.


Module WalkProof (Kalloc : KALLOC) (MemsetArray : MEMSET) : WALK.

Section ProofWalk.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  (* NOTE: no shared [Context `{GEN : GenId} `{CID : CpuId}] here -- the epilogue/tail/probe/
     alloc/loop lemmas below apply EACH OTHER at a hart that a [wp_next]
     crossing may have migrated to, so each needs its OWN implicit per-lemma
     [CID] binder (shadowing what a section Context would give) rather than
     sharing one rigid section-wide hart; see the porting guide's "Two things
     a DECOMPOSED proof needs". *)


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

  (* ================================================================= *)
  (* THE SHARED EPILOGUE (+0x52..+0x64) -- sconf mirror.                 *)
  (* ================================================================= *)
  Lemma wp_walk_epilogue_sconf `{GEN : GenId} `{CID : CpuId} (γa : gname)
      (mm Mf : regfile) (t tf : ptree) (K : nat) (lvl : nat)
      (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (q : nat) (b : bool) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (22 <= K)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    ptree_same_rep0 t tf ->
    ptree_offpath_eq vpn t tf ->
    pt_present_mono t tf ->
    pt_nodes tf = (pt_nodes t + q)%nat ->
    (q <= pt_missing t vpn 1)%nat ->
    (((Mf !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0)
        /\ avail_zero (avail_sub on q))
     \/ (exists p2 p1 w0, ptree_level0 tf vpn p2 p1 w0
          /\ Mf !!! Regidx (mword_of_int 10 : mword 5) = pt_addr0 p1 vpn)) ->
    sie_cap_gpr Mf (K - 8)%nat b p -∗ cpu_own lvl eb p C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.walk + 0x52)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γa (avail_sub on q) -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g : nat),
      sie_cap_gpr mr K b p -∗ cpu_own lvl eb p C b -∗
      pc_is ret_tgt -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗
      kalloc_env γa (avail_sub on g) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ptree_same_rep0 t t'⌝ -∗
      ⌜ptree_offpath_eq vpn t t'⌝ -∗
      ⌜pt_present_mono t t'⌝ -∗
      ⌜(g <= pt_missing t vpn 1)%nat⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0
           /\ avail_zero (avail_sub on g))
        \/ (exists p2 p1 w0,
             ptree_level0 t' vpn p2 p1 w0 /\
             mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va vpn sp0 spr ret_tgt HK Hsp Hx23 Hx24 Hx25 Hx26 Hx27 Hsame Hoff Hpres Hnodes Hmiss Hpay.
    iIntros "Hcg Hcnt #Htext Hpc
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
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x52)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
              Mf (K - 8)%nat (mm !!! Regidx (mword_of_int 1 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi52 [Hc56] [-]").
    { iEval (rewrite HspMf Hb1). iExact "Hc56". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hc56".
    iEval (rewrite HspMf Hb1) in "Hc56".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> Mf).
    assert (Hpp52n : add_vec_int (mword_of_int (KernelSyms.walk + 0x52) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52n) in "Hpc".
    (* +0x54 c.ldsp x8,48(sp) *)
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
    { rewrite /E1. rewrite upd_ne; [| reg_neq]. exact HspMf. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x54)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 8)%nat (mm !!! Regidx (mword_of_int 8 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54 [Hc48] [-]").
    { iEval (rewrite HspE1 Hb2). iExact "Hc48". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hc48".
    iEval (rewrite HspE1 Hb2) in "Hc48".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (Hpp54n : add_vec_int (mword_of_int (KernelSyms.walk + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54n) in "Hpc".
    (* +0x56 c.ldsp x9,40(sp) *)
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spr).
    { rewrite /E2. rewrite upd_ne; [| reg_neq]. exact HspE1. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x56)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 8)%nat (mm !!! Regidx (mword_of_int 9 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi56 [Hc40] [-]").
    { iEval (rewrite HspE2 Hb3). iExact "Hc40". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hc40".
    iEval (rewrite HspE2 Hb3) in "Hc40".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (Hpp56n : add_vec_int (mword_of_int (KernelSyms.walk + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56n) in "Hpc".
    (* +0x58 c.ldsp x18,32(sp) *)
    assert (HspE3 : E3 !!! Regidx csp_rs1 = spr).
    { rewrite /E3. rewrite upd_ne; [| reg_neq]. exact HspE2. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x58)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              E3 (K - 8)%nat (mm !!! Regidx (mword_of_int 18 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi58 [Hc32] [-]").
    { iEval (rewrite HspE3 Hb4). iExact "Hc32". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hc32".
    iEval (rewrite HspE3 Hb4) in "Hc32".
    set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 18 : mword 5))]> E3).
    assert (Hpp58n : add_vec_int (mword_of_int (KernelSyms.walk + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58n) in "Hpc".
    (* +0x5a c.ldsp x19,24(sp) *)
    assert (HspE4 : E4 !!! Regidx csp_rs1 = spr).
    { rewrite /E4. rewrite upd_ne; [| reg_neq]. exact HspE3. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x5a)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              E4 (K - 8)%nat (mm !!! Regidx (mword_of_int 19 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a [Hc24] [-]").
    { iEval (rewrite HspE4 Hb5). iExact "Hc24". }
    iIntros (CIDe5 Hse5) "Hcg Hpc Hc24".
    iEval (rewrite HspE4 Hb5) in "Hc24".
    set (E5 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 19 : mword 5))]> E4).
    assert (Hpp5an : add_vec_int (mword_of_int (KernelSyms.walk + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5an) in "Hpc".
    (* +0x5c c.ldsp x20,16(sp) *)
    assert (HspE5 : E5 !!! Regidx csp_rs1 = spr).
    { rewrite /E5. rewrite upd_ne; [| reg_neq]. exact HspE4. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x5c)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              E5 (K - 8)%nat (mm !!! Regidx (mword_of_int 20 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5c [Hc16] [-]").
    { iEval (rewrite HspE5 Hb6). iExact "Hc16". }
    iIntros (CIDe6 Hse6) "Hcg Hpc Hc16".
    iEval (rewrite HspE5 Hb6) in "Hc16".
    set (E6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 20 : mword 5))]> E5).
    assert (Hpp5cn : add_vec_int (mword_of_int (KernelSyms.walk + 0x5c) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5cn) in "Hpc".
    (* +0x5e c.ldsp x21,8(sp) *)
    assert (HspE6 : E6 !!! Regidx csp_rs1 = spr).
    { rewrite /E6. rewrite upd_ne; [| reg_neq]. exact HspE5. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x5e)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              E6 (K - 8)%nat (mm !!! Regidx (mword_of_int 21 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5e [Hc08] [-]").
    { iEval (rewrite HspE6 Hb7). iExact "Hc08". }
    iIntros (CIDe7 Hse7) "Hcg Hpc Hc08".
    iEval (rewrite HspE6 Hb7) in "Hc08".
    set (E7 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 21 : mword 5))]> E6).
    assert (Hpp5en : add_vec_int (mword_of_int (KernelSyms.walk + 0x5e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5en) in "Hpc".
    (* +0x60 c.ldsp x22,0(sp) *)
    assert (HspE7 : E7 !!! Regidx csp_rs1 = spr).
    { rewrite /E7. rewrite upd_ne; [| reg_neq]. exact HspE6. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walk + 0x60)) (mword_of_int 0 : mword 6) (mword_of_int 22 : mword 5)
              E7 (K - 8)%nat (mm !!! Regidx (mword_of_int 22 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi60 [Hc00] [-]").
    { iEval (rewrite HspE7 Hb8). iExact "Hc00". }
    iIntros (CIDe8 Hse8) "Hcg Hpc Hc00".
    iEval (rewrite HspE7 Hb8) in "Hc00".
    set (E8 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 22 : mword 5))]> E7).
    assert (Hpp60n : add_vec_int (mword_of_int (KernelSyms.walk + 0x60) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60n) in "Hpc".
    assert (HspE8 : E8 !!! Regidx csp_rs1 = spr).
    { rewrite /E8. rewrite upd_ne; [| reg_neq]. exact HspE7. }
    (* +0x62 c.addi16sp sp,+64 -- the frame pop (feed 8 slots back into avail) *)
    set (E9 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E8).
    assert (HspE9 : E9 !!! Regidx csp_rs1 = sp0).
    { rewrite /E9 upd_eq. rewrite HspE8. unfold spr. apply frame_cancel_64. }
    assert (Hwv : add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0).
    { rewrite HspE8. unfold spr. apply frame_cancel_64. }
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
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.walk + 0x62)) (mword_of_int 4 : mword 6)
              E8 (K - 8)%nat 8 b Hpop
              with "Hcg Hpc Hi62 Hframe [-]").
    iIntros (CIDe9 Hse9) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E8) with E9.
    assert (Hnk : ((K - 8) + 8)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.walk + 0x62) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    (* +0x64 ret *)
    assert (HE9ra : E9 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { peel_reg. }
    assert (Hrt : ret_pc (E9 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt).
    { rewrite HE9ra. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.walk + 0x64)) (mword_of_int 1 : mword 5) E9 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi64 [-]").
    iIntros (CIDe10 Hse10) "Hcg Hpc".
    iEval (rewrite Hrt) in "Hpc".
    iSpecialize ("Hcont" $! CIDe10 with "[%]"); [wp_next_chain|].
    assert (HcntCE : b = false \/ p = zero_reg -> (CIDe10 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (cpu_own_transport CID CIDe10 lvl eb p C b HcntCE with "Hcnt") as "Hcnt".
    iApply ("Hcont" $! E9 tf q with "Hcg Hcnt Hpc Hptree [%] Henv [%] [%] [%] [%] [%] [%]").
    { exact Hnodes. }
    { (* callee_saved mm E9 *)
      unfold callee_saved.
      split.
      { rewrite /E9 upd_eq. rewrite HspE8. unfold spr. apply frame_cancel_64. }
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
    { exact Hoff. }
    { exact Hpres. }
    { exact Hmiss. }
    { assert (HE9a0 : E9 !!! Regidx (mword_of_int 10 : mword 5)
                      = Mf !!! Regidx (mword_of_int 10 : mword 5)).
      { peel_reg. }
      rewrite HE9a0. exact Hpay. }
  Qed.

  (* ================================================================= *)
  (* THE SHARED TAIL (+0x46..+0x50) -- sconf mirror.                     *)
  (* ================================================================= *)
  Lemma wp_walk_tail_sconf `{GEN : GenId} `{CID : CpuId} (γa : gname)
      (mm Mf : regfile) (t tf : ptree) (b0 : mword 44) (K : nat) (lvl : nat)
      (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (q : nat) (b : bool) :
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
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    ptree_same_rep0 t tf ->
    ptree_offpath_eq vpn t tf ->
    pt_present_mono t tf ->
    pt_nodes tf = (pt_nodes t + q)%nat ->
    (q <= pt_missing t vpn 1)%nat ->
    (exists p2 p1 w0, ptree_level0 tf vpn p2 p1 w0
       /\ pt_addr0 p1 vpn = u_pte_addr b0 (vpn_idx 0 vpn)) ->
    sie_cap_gpr Mf (K - 8)%nat b p -∗ cpu_own lvl eb p C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.walk + 0x46)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γa (avail_sub on q) -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g : nat),
      sie_cap_gpr mr K b p -∗ cpu_own lvl eb p C b -∗
      pc_is ret_tgt -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗
      kalloc_env γa (avail_sub on g) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ptree_same_rep0 t t'⌝ -∗
      ⌜ptree_offpath_eq vpn t t'⌝ -∗
      ⌜pt_present_mono t t'⌝ -∗
      ⌜(g <= pt_missing t vpn 1)%nat⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0
           /\ avail_zero (avail_sub on g))
        \/ (exists p2 p1 w0,
             ptree_level0 t' vpn p2 p1 w0 /\
             mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va vpn sp0 spr ret_tgt HK Hva' Hsp Hs3 Hs1 Hx23 Hx24 Hx25 Hx26 Hx27 Hsame Hoff Hpres Hnodes Hmiss Hlvl.
    iIntros "Hcg Hcnt #Htext Hpc
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hptree Henv Hcont".
    iPoseProof (wi_46 with "Htext") as "Hi46".
    iPoseProof (wi_4a with "Htext") as "Hi4a".
    iPoseProof (wi_4e with "Htext") as "Hi4e".
    iPoseProof (wi_50 with "Htext") as "Hi50".
    (* +0x46 srli a0,s3,12 *)
    iApply (wp_srli4_s_sconf (mword_of_int (KernelSyms.walk + 0x46)) (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 12 : mword 6)
              Mf (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi46 [-]").
    iIntros (CIDt1 Hst1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (T1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (shift_bits_right (Mf !!! Regidx (mword_of_int 19 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> Mf).
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.walk + 0x46) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* +0x4a andi a0,a0,511 *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.walk + 0x4a)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 511 : mword 12)
              (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                       (sign_extend' 64 (mword_of_int 511 : mword 12)))
              T1 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite /T1 upd_eq; rewrite Hs3; reflexivity)
              with "Hcg Hpc Hi4a [-]").
    iIntros (CIDt2 Hst2) "Hcg Hpc".
    set (T2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (mword_of_int 511 : mword 12)))]> T1).
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.walk + 0x4a) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    (* +0x4e c.slli a0,3 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.walk + 0x4e)) (Regidx (mword_of_int 10 : mword 5)) (mword_of_int 10 : mword 5) (mword_of_int 3 : mword 6)
              T2 (K - 8)%nat b
              ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4e [-]").
    iIntros (CIDt3 Hst3) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (T3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (shift_bits_left (T2 !!! Regidx (mword_of_int 10 : mword 5)) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> T2).
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.walk + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 c.add a0,s1 *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.walk + 0x50)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              T3 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi50 [-]").
    iIntros (CIDt4 Hst4) "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
    set (T4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (T3 !!! Regidx (mword_of_int 10 : mword 5)) (T3 !!! Regidx (mword_of_int 9 : mword 5)))]> T3).
    assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.walk + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
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
    (* funnel into the shared epilogue -- [Hcont]/[Hcnt] were anchored at
       THIS lemma's entry hart [CID]; the four plain instructions above
       (srli/andi/cslli/cadd) each landed on a fresh generic-[b] hart,
       ending at [CIDt4] -- re-anchor both once via the composed chain. *)
    assert (Hchaint : b = false \/ p = zero_reg -> (CIDt4 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift Hchaint with "Hcont") as "Hcont".
    iDestruct (cpu_own_transport CID CIDt4 lvl eb p C b Hchaint with "Hcnt") as "Hcnt".
    iApply (wp_walk_epilogue_sconf γa mm T4 t tf K lvl eb p C on q b HK
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    exact Hsp)
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
              Hsame Hoff Hpres Hnodes Hmiss
              ltac:(destruct Hlvl as (p2 & p1 & w0 & Hl0 & Heq);
                    right; exists p2, p1, w0; split;
                    [exact Hl0 | rewrite HT4a0 Heq; reflexivity])
              with "Hcg Hcnt Htext Hpc
                    Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                    Hptree Henv Hcont").
  Qed.

  (* ================================================================= *)
  (* THE LOOP BODY'S STRAIGHT-LINE CORE (+0x26..+0x36) -- sconf mirror.  *)
  (* ================================================================= *)
  Lemma wp_walk_probe_sconf `{GEN : GenId} `{CID : CpuId}
      (M : regfile) (n : nat) (va shift : mword 64) (slotaddr pte : mword 64) (b : bool) (p : mword 64) {dqm : dfrac} :
    M !!! Regidx (mword_of_int 19 : mword 5) = va ->
    M !!! Regidx (mword_of_int 20 : mword 5) = shift ->
    add_vec
      (shift_bits_left
         (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                  (sign_extend' 64 (mword_of_int 511 : mword 12)))
         (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
      (M !!! Regidx (mword_of_int 9 : mword 5)) = slotaddr ->
    sie_cap_gpr M n b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.walk + 0x26)) -∗
    slotaddr ↦₈{dqm} pte -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (and_vec pte (sign_extend' 64 (mword_of_int 1 : mword 12)))]>
                (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg pte]>
                 (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg slotaddr]> M))) n b p -∗
      pc_is (mword_of_int (KernelSyms.walk + 0x3a)) -∗
      slotaddr ↦₈{dqm} pte -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hs3 Hs4 Hslot.
    iIntros "Hcg #Htext Hpc Hown Hcont".
    iPoseProof (wi_26 with "Htext") as "Hi26".
    iPoseProof (wi_2a with "Htext") as "Hi2a".
    iPoseProof (wi_2e with "Htext") as "Hi2e".
    iPoseProof (wi_30 with "Htext") as "Hi30".
    iPoseProof (wi_32 with "Htext") as "Hi32".
    iPoseProof (wi_36 with "Htext") as "Hi36".
    (* +0x26 srl s2,s3,s4 *)
    iApply (wp_srl_s_sconf (mword_of_int (KernelSyms.walk + 0x26)) (mword_of_int 18 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 20 : mword 5)
              (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
              M n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite Hs3 Hs4; reflexivity)
              with "Hcg Hpc Hi26 [-]").
    iIntros (CIDq1 Hsq1) "Hcg Hpc".
    set (L1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))]> M).
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.walk + 0x26) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a andi s2,s2,511 *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.walk + 0x2a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 511 : mword 12)
              (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                       (sign_extend' 64 (mword_of_int 511 : mword 12)))
              L1 n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite /L1 upd_eq; reflexivity)
              with "Hcg Hpc Hi2a [-]").
    iIntros (CIDq2 Hsq2) "Hcg Hpc".
    set (L2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (mword_of_int 511 : mword 12)))]> L1).
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.walk + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.slli s2,3 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.walk + 0x2e)) (Regidx (mword_of_int 18 : mword 5)) (mword_of_int 18 : mword 5) (mword_of_int 3 : mword 6)
              L2 n b
              ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e [-]").
    iIntros (CIDq3 Hsq3) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (L3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_left (L2 !!! Regidx (mword_of_int 18 : mword 5)) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> L2).
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.walk + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.add s2,s1 *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.walk + 0x30)) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
              L3 n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 [-]").
    iIntros (CIDq4 Hsq4) "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.walk + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
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
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.walk + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
              L4 n pte b (dqm:=dqm)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32 [Hown] [-]").
    { iEval (rgne; rewrite Hea0 HL4s2). iExact "Hown". }
    iIntros (CIDq5 Hsq5) "Hcg Hpc Hown".
    iEval (rgne; rewrite Hea0 HL4s2) in "Hown".
    set (L5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg pte]> L4).
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.walk + 0x32) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 andi a5,s1,1 *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.walk + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
              (and_vec pte (sign_extend' 64 (mword_of_int 1 : mword 12)))
              L5 n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite /L5 upd_eq; reflexivity)
              with "Hcg Hpc Hi36 [-]").
    iIntros (CIDq6 Hsq6) "Hcg Hpc".
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.walk + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    iSpecialize ("Hcont" $! CIDq6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" with "Hcg Hpc Hown").
  Qed.

  (* ===== memset-zero page wrapper (keeps the zeroed bytes) ===== *)
  Lemma wp_memset_page_zero_sconf `{GEN : GenId} `{CID : CpuId}
      (m0 : regfile) (n : nat) (cval : mword 64) (b : bool) (pcur : mword 64) :
    let a0_idx : mword 5 := mword_of_int 10 in
    let a1_idx : mword 5 := mword_of_int 11 in
    let a2_idx : mword 5 := mword_of_int 12 in
    let pcE := mword_of_int KernelSyms.memset in
    let sp0 := m0 !!! Regidx csp_rs1 in
    let ra0 := m0 !!! Regidx (mword_of_int 1 : mword 5) in
    let p := m0 !!! Regidx a0_idx in
    let ret_tgt := ret_pc ra0 in
    let cbyte := nth_byte (autocast (T := mword) (subrange_vec_dec cval (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 in
    m0 !!! Regidx a1_idx = cval ->
    m0 !!! Regidx a2_idx = (mword_of_int 4096 : mword 64) ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    (2 <= n)%nat ->
    sie_cap_gpr m0 n b pcur -∗
    kernel_text -∗ pc_is pcE -∗
    page_own p -∗
    wp_next b pcur (fun (CID : CpuId) =>
    ∀ mfin,
      sie_cap_gpr mfin n b pcur -∗
      pc_is ret_tgt -∗
      ([∗ list] j ∈ seq 0 4096, (pa_add p j) ↦ₘ cbyte) -∗
      ⌜ callee_saved m0 mfin ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros a0_idx a1_idx a2_idx pcE sp0 ra0 p ret_tgt cbyte Hcval Ha2 Hret0 Hn.
    iIntros "Hcg #Htext Hpc Hpage Hcont".
    (* bridge [page_own p] to memset's per-byte buffer, then hand it to the
       general array-memset spec at len = 4096 (KEEPING the written bytes). *)
    iEval (rewrite /page_own /byte_any) in "Hpage".
    iDestruct (bytes_choose 4096 0 (fun j b => ((pa_add p j) ↦ₘ b)%I) with "Hpage")
      as (olds) "Hbuf".
    assert (Ha2' : m0 !!! Regidx a2_idx = (mword_of_int (Z.of_nat 4096) : mword 64))
      by (rewrite Ha2; f_equal; vm_compute; reflexivity).
    iApply (MemsetArray.wp_memset_sconf m0 n 4096 cval olds b pcur
              Hn ltac:(vm_compute; reflexivity) Hcval Ha2'
              with "Hcg Htext Hpc [Hbuf] [-]").
    { iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H". iExact "H". }
    iIntros (CIDm Hsm mfin) "Hcg Hpc Hbuf %Hcs".
    iSpecialize ("Hcont" $! CIDm with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mfin with "Hcg Hpc Hbuf [%]").
    exact Hcs.
  Qed.

  (* ================================================================= *)
  (* THE SHARED ALLOCATION ARM (+0x72..+0x94) -- sconf mirror.           *)
  (* ================================================================= *)
  Lemma wp_walk_alloc_sconf `{GEN : GenId} `{CID : CpuId} (γa : gname)
      (mm Mf : regfile) (tf : ptree)
      (tG : mword 44 -> ptree) (N clvl : nat)
      (cellA : mword 64) (w0 : bv 64) (K : nat) (lvl : nat)
      (eb : bool) (p : mword 64) (C : iProp Σ) (F : iProp Σ)
      (on : option nat) (g : nat) (b : bool) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (* kalloc's transient noff increment stays in int range *)
    (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
    (22 <= K)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 18 : mword 5) = cellA ->
    eq_vec (Mf !!! Regidx (mword_of_int 22 : mword 5)) zero_reg = false ->
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    (ptree_own N (DfracOwn 1) tf ⊢
       cellA ↦₈ w0 ∗
       (∀ bn : mword 44,
          cellA ↦₈ pt_ptr_pte bn -∗
          ptree_own clvl (DfracOwn 1) (pt_empty_node bn) -∗
          ptree_own N (DfracOwn 1) (tG bn))) ->
    sie_cap_gpr Mf (K - 8)%nat b p -∗ cpu_own lvl eb p C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.walk + 0x72)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    ptree_own N (DfracOwn 1) tf -∗
    kalloc_env γa (avail_sub on g) -∗
    F -∗
    (* SUCCESS: page allocated, grafted; rejoin the loop at +0x40 *)
    wp_next b p (fun (CID : CpuId) =>
    ∀ (Mo : regfile) (bn : mword 44),
      ⌜forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
         Mo !!! Regidx c = Mf !!! Regidx c⌝ -∗
      ⌜Mo !!! Regidx (mword_of_int 9 : mword 5)
         = zero_extend' 64 (concat_vec bn (zeros' 12 : mword 12))⌝ -∗
      sie_cap_gpr Mo (K - 8)%nat b p -∗ cpu_own lvl eb p C b -∗
      pc_is (mword_of_int (KernelSyms.walk + 0x40)) -∗
      pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
      pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
      pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
      pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
      pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
      pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
      pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
      pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
      ptree_own N (DfracOwn 1) (tG bn) -∗
      kalloc_env γa (avail_sub on (S g)) -∗
      F -∗
      WP (Loop : expr riscv_lang)) -∗
    (* FAILURE: kalloc returned 0; the tree is untouched, exit at +0x52 *)
    wp_next b p (fun (CID : CpuId) =>
    ∀ (Mo : regfile),
      ⌜forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
         Mo !!! Regidx c = Mf !!! Regidx c⌝ -∗
      ⌜Mo !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0⌝ -∗
      ⌜avail_zero (avail_sub on g)⌝ -∗
      sie_cap_gpr Mo (K - 8)%nat b p -∗ cpu_own lvl eb p C b -∗
      pc_is (mword_of_int (KernelSyms.walk + 0x52)) -∗
      pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
      pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
      pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
      pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
      pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
      pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
      pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
      pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
      ptree_own N (DfracOwn 1) tf -∗
      kalloc_env γa (avail_sub on g) -∗
      F -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va vpn sp0 spr ret_tgt Hlvl HK Hsp Hs2c Hs6 Hx23 Hx24 Hx25 Hx26 Hx27 Hacc.
    iIntros "Hcg Hcnt #Htext Hpc
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hptree Henv HF Hok Hfail".
    iPoseProof (wi_72 with "Htext") as "Hi72".
    iPoseProof (wi_76 with "Htext") as "Hi76".
    iPoseProof (wi_7a with "Htext") as "Hi7a".
    iPoseProof (wi_7c with "Htext") as "Hi7c".
    (* +0x72 beqz s6 FALLS (alloc = 1) *)
    iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.walk + 0x72)) (mword_of_int 36 : mword 13) (mword_of_int 22 : mword 5)
              Mf (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rgne; exact Hs6)
              with "Hcg Hpc Hi72 [-]").
    iIntros (CIDa1 Hsa1) "Hcg Hpc".
    assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.walk + 0x72) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp76) in "Hpc".
    (* +0x76 jal kalloc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.walk + 0x76)) (mword_of_int 1 : mword 5) (mword_of_int 2095962 : mword 21)
              Mf (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi76 [-]").
    iIntros (CIDa2 Hsa2) "Hcg Hpc".
    set (J := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.walk + 0x76) : mword 64) 4)]> Mf).
    assert (Htgtk : add_vec (mword_of_int (KernelSyms.walk + 0x76) : mword 64) (sign_extend' 64 (mword_of_int 2095962 : mword 21)) = mword_of_int KernelSyms.kalloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtk) in "Hpc".
    (* ---- kalloc() through the env bundle ---- *)
    iDestruct "Henv" as (γk) "(#Hlock & Havail & #Hqcpu)".
    assert (HspJ : J !!! Regidx csp_rs1 = spr).
    { rewrite /J. rewrite upd_ne; [| reg_neq]. exact Hsp. }
    assert (HJ1 : J !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.walk + 0x76) : mword 64) 4)
      by (rewrite /J upd_eq; reflexivity).
    (* [Hcnt] entered this lemma at [CID]; the [beqz]/[jal] pair landed on
       [CIDa2] -- transport it once before feeding kalloc. *)
    assert (HcntCA0 : b = false \/ p = zero_reg -> (CIDa2 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (cpu_own_transport CID CIDa2 lvl eb p C b HcntCA0 with "Hcnt") as "Hcnt".
    iApply (Kalloc.wp_kalloc_sconf γa γk (mword_of_int (KernelSyms.kmem + 24))
              J (avail_sub on g) lvl eb p C (K - 8)%nat b
              ltac:(lia)
              ltac:(reflexivity)
              Hlvl
              with "Hcg Hcnt Htext Hpc Hlock Havail Hqcpu [-]").
    iIntros (CIDa3 Hsa3 mr) "Hcg Hcnt Hpc %Hkcs Hkpost".
    (* the return pc: +0x7a *)
    assert (Hret7a : ret_pc (J !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.walk + 0x7a)).
    { rewrite HJ1. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret7a) in "Hpc".
    (* +0x7a c.mv s1,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.walk + 0x7a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mr (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7a [-]").
    iIntros (CIDa4 Hsa4) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mr !!! Regidx (mword_of_int 10 : mword 5)))]> mr).
    assert (Hpp7c : add_vec_int (mword_of_int (KernelSyms.walk + 0x7a) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7c) in "Hpc".
    (* +0x7c c.beqz a0: the null/success split *)
    iDestruct "Hkpost" as "[(%Hnull & %Hz & Havail2) | (%Hpv & Hpage & Havail2)]".
    { (* ---- NULL: exit through the epilogue with a0 = 0 ---- *)
      (* rebuild kalloc_env from the cpu cell, count unchanged *)
      iAssert (kalloc_env γa (avail_sub on g))
        with "[Havail2]" as "Henv".
      { iExists γk. iFrame "Hlock Havail2 Hqcpu". }
      assert (HN1a0 : N1 !!! Regidx (mword_of_int 10 : mword 5) = mr !!! Regidx (mword_of_int 10 : mword 5)).
      { rewrite /N1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.walk + 0x7c)) (mword_of_int 235 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
                N1 (K - 8)%nat b
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HN1a0 Hnull; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi7c [-]").
      iIntros (CIDa5 Hsa5). iNext. iIntros "Hcg Hpc".
      assert (Htgt52 : add_vec (mword_of_int (KernelSyms.walk + 0x7c) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 235 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.walk + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt52) in "Hpc".
      (* "Hfail" (like "Hok") was never touched, so it is STILL anchored at
         this lemma's entry hart [CID]; [Hcnt] on the other hand was
         REFRESHED at [CIDa3] by kalloc's own postcondition -- each needs
         its own link to [CIDa5]. *)
      assert (HcntCA1 : b = false \/ p = zero_reg -> (CIDa5 : CPU) = (CID : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift HcntCA1 with "Hfail") as "Hfail".
      assert (HcntCA1' : b = false \/ p = zero_reg -> (CIDa5 : CPU) = (CIDa3 : CPU)) by wp_next_chain.
      iDestruct (cpu_own_transport CIDa3 CIDa5 lvl eb p C b HcntCA1' with "Hcnt") as "Hcnt".
      iSpecialize ("Hfail" $! CIDa5 with "[%]"); [wp_next_chain|].
      iApply ("Hfail" $! N1 with "[%] [%] [%] Hcg Hcnt Hpc
                Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hptree Henv HF").
      { intros c Hcs Hc9.
        rewrite /N1. rewrite upd_ne;
          [| intros Habs; injection Habs as Habs2; exact (Hc9 Habs2)].
        rewrite (callee_saved_lookup Hkcs c Hcs).
        rewrite /J. rewrite upd_ne;
          [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hcs; discriminate].
        reflexivity. }
      { rewrite HN1a0 Hnull; reflexivity. }
      { exact Hz. } }
    (* ---- SUCCESS: page p, memset(0), graft, store, rejoin ---- *)
    (* rebuild kalloc_env from the cpu cell, count decremented one step *)
    iAssert (kalloc_env γa (avail_sub on (S g)))
      with "[Havail2]" as "Henv".
    { rewrite avail_sub_S. iExists γk. iFrame "Hlock Havail2 Hqcpu". }
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
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.walk + 0x7c)) (mword_of_int 235 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              N1 (K - 8)%nat b
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HN1a0; apply eq_vec_false_iff; rewrite Hnz;
                    exact (page_valid_ne_null _ Hpv))
              with "Hcg Hpc Hi7c [-]").
    iIntros (CIDa5b Hsa5b) "Hcg Hpc".
    assert (Hpp7e : add_vec_int (mword_of_int (KernelSyms.walk + 0x7c) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7e) in "Hpc".
    (* +0x7e c.lui a2,1 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.walk + 0x7e)) (mword_of_int 12 : mword 5)
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              N1 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi7e [-]").
    iIntros (CIDa6 Hsa6) "Hcg Hpc".
    set (N2 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 4096 : mword 64)]> N1).
    assert (Hpp80 : add_vec_int (mword_of_int (KernelSyms.walk + 0x7e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp80) in "Hpc".
    (* +0x80 c.li a1,0 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.walk + 0x80)) (mword_of_int 11 : mword 5) (mword_of_int 0 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
              N2 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(reflexivity)
              with "Hcg Hpc Hi80 [-]").
    iIntros (CIDa7 Hsa7) "Hcg Hpc".
    set (N3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> N2).
    assert (Hpp82 : add_vec_int (mword_of_int (KernelSyms.walk + 0x80) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp82) in "Hpc".
    (* +0x82 jal memset *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.walk + 0x82)) (mword_of_int 1 : mword 5) (mword_of_int 2096360 : mword 21)
              N3 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi82 [-]").
    iIntros (CIDa8 Hsa8) "Hcg Hpc".
    set (N4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.walk + 0x82) : mword 64) 4)]> N3).
    assert (Htgtm : add_vec (mword_of_int (KernelSyms.walk + 0x82) : mword 64) (sign_extend' 64 (mword_of_int 2096360 : mword 21)) = mword_of_int KernelSyms.memset)
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
    iApply (wp_memset_page_zero_sconf N4 (K - 8)%nat (mword_of_int 0 : mword 64) b p
              ltac:(rewrite /N4; rewrite upd_ne; [| reg_neq];
                    rewrite /N3 upd_eq; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /N4 /N3;
                    repeat (rewrite upd_ne; [| reg_neq]);
                    rewrite upd_eq; reflexivity)
              ltac:(rewrite /N4 upd_eq; vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc [Hpage] [-]").
    { iEval (rewrite HN4a0). iExact "Hpage". }
    iIntros (CIDa9 Hsa9 mfin) "Hcg Hpc Hbytes %Hmcs".
    assert (Hret86 : ret_pc (N4 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.walk + 0x86)).
    { rewrite /N4 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret86) in "Hpc".
    (* the zero page as a description node *)
    assert (Hcb : nth_byte (autocast (T := mword) (subrange_vec_dec (mword_of_int 0 : mword 64) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 = (mword_of_int 0 : mword 8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hcb HN4a0) in "Hbytes".
    (* the kalloc page is ↦ₘ (VA tier); [ptree_own] is PHYSICAL tier, so
       disassemble the identity kdata page to ↦ₚ before grafting it as a node.
       The static-claims bundle comes off the persistent [hw_config] head of
       the threaded [sie_cap_gpr]. *)
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
    iDestruct "Hhwc" as (hwmisa0 hwmseccfg0 hwpmar0 hwelp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb)".
    iDestruct (mem_page_to_phys (mr !!! Regidx (mword_of_int 10 : mword 5)) (DfracOwn 1) (mword_of_int 0 : mword 8)
                 ltac:(intros j Hj; apply kdata_svpn_class;
                       apply page_in_range_addr_is_kdata; [exact Hpv | exact Hj])
                 with "Hkmapb Hbytes") as "Hbytes".
    iEval (rewrite -Hpb) in "Hbytes".
    (* the freshly-allocated PT page's identity claim (uniform-claims PHYSICAL
       TIER): it is a kdata page, so [pt_node_claim bppn] comes off the static
       bundle -- what [zero_page_to_node] now needs to build the node. *)
    assert (Hnpv : page_valid (page_base bppn)).
    { unfold page_base. rewrite Hpb. exact Hpv. }
    iDestruct (pt_node_claim_from_static bppn Hnpv with "Hkmapb") as "#Hbclaim".
    iDestruct (zero_page_to_node clvl (DfracOwn 1) bppn with "Hbclaim Hbytes") as "Hchild".
    (* +0x86 srli a5,s1,12 *)
    assert (Hmfs1 : mfin !!! Regidx (mword_of_int 9 : mword 5)
                    = add_vec zero_reg (mr !!! Regidx (mword_of_int 10 : mword 5))).
    { rewrite (callee_saved_lookup Hmcs (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /N4 /N3 /N2.
      repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /N1 upd_eq. reflexivity. }
    iApply (wp_srli4_s_sconf (mword_of_int (KernelSyms.walk + 0x86)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
              mfin (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi86 [-]").
    iIntros (CIDa10 Hsa10) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (mfin !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> mfin).
    assert (Hpp8a : add_vec_int (mword_of_int (KernelSyms.walk + 0x86) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8a) in "Hpc".
    (* +0x8a c.slli a5,10 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.walk + 0x8a)) (Regidx (mword_of_int 15 : mword 5)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 6)
              P1 (K - 8)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8a [-]").
    iIntros (CIDa11 Hsa11) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (P1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> P1).
    assert (Hpp8c : add_vec_int (mword_of_int (KernelSyms.walk + 0x8a) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8c) in "Hpc".
    (* +0x8c ori a5,a5,1 *)
    iApply (wp_ori_s_sconf (mword_of_int (KernelSyms.walk + 0x8c)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 12)
              (or_vec (P2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
              P2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; reflexivity)
              with "Hcg Hpc Hi8c [-]").
    iIntros (CIDa12 Hsa12) "Hcg Hpc".
    set (P3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (or_vec (P2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> P2).
    assert (Hpp90 : add_vec_int (mword_of_int (KernelSyms.walk + 0x8c) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
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
    iApply (wp_sd_s_sconf (mword_of_int (KernelSyms.walk + 0x90)) (mword_of_int 15 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
              P3 (K - 8)%nat w0 b
              with "Hcg Hpc Hi90 [Hcell] [-]").
    { iEval (rgne; rewrite Hea0' HP3s2). iExact "Hcell". }
    iIntros (CIDa13 Hsa13) "Hcg Hpc Hcell".
    iEval (rgne; rgne; rewrite Hea0' HP3s2 HP3a5) in "Hcell".
    iDestruct ("Hgw" $! bppn with "Hcell Hchild") as "Hptree".
    assert (Hpp94 : add_vec_int (mword_of_int (KernelSyms.walk + 0x90) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp94) in "Hpc".
    (* +0x94 c.j back to the loop decrement at +0x40 *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.walk + 0x94))
              (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0")))
              P3 (K - 8)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi94 [-]").
    iIntros (CIDa14 Hsa14). iNext. iIntros "Hcg Hpc".
    assert (Htgt40 : add_vec (mword_of_int (KernelSyms.walk + 0x94) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.walk + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt40) in "Hpc".
    (* hand off to the success continuation *)
    (* [Hcont]-analogue "Hok" was anchored at [CID]; the SUCCESS arm's
       thirteen plain instructions (cbeqz.fall through cj) all landed on
       fresh generic-[b] harts, ending at [CIDa14] -- re-anchor once. *)
    assert (HcntCA2 : b = false \/ p = zero_reg -> (CIDa14 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift HcntCA2 with "Hok") as "Hok".
    assert (HcntCA2' : b = false \/ p = zero_reg -> (CIDa14 : CPU) = (CIDa3 : CPU)) by wp_next_chain.
    iDestruct (cpu_own_transport CIDa3 CIDa14 lvl eb p C b HcntCA2' with "Hcnt") as "Hcnt".
    iSpecialize ("Hok" $! CIDa14 with "[%]"); [wp_next_chain|].
    iApply ("Hok" $! P3 bppn with "[%] [%] Hcg Hcnt Hpc
            Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hptree Henv HF").
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
  (* the loop counter [s4 = 12 + 9*level] decrements by 9 (addiw -9), staying
     inside 32 bits since level <= 2. *)
  Local Lemma walk_caddiw_dec9 (L' : nat) : (1 <= S L' <= 2)%nat ->
    sign_extend' 64 (subrange_vec_dec
      (add_vec (mword_of_int (12 + 9 * Z.of_nat (S L')) : mword 64)
               (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0)
    = mword_of_int (12 + 9 * Z.of_nat L').
  Proof.
    intros HL. destruct L' as [| [| k]].
    - apply bv_eq; vm_compute; reflexivity.
    - apply bv_eq; vm_compute; reflexivity.
    - exfalso; lia.
  Qed.

  (* fuel-generic walk loop *)
  (* ============================================================= *)
  (* BLOCKED (explicit-cpuid port, time-boxed): wp_walk_loop_sconf and below LEFT IN THEIR PRE-PORT FORM.

     Everything ABOVE this point in the file (wp_walk_epilogue_sconf,
     wp_walk_tail_sconf, wp_walk_probe_sconf, wp_memset_page_zero_sconf,
     wp_walk_alloc_sconf) has been fully ported to the explicit-cpuid
     interface and independently verified by [coqc] (each compiles
     standalone up through its own Qed, one file-truncation check per
     lemma; see the porting session's log).  That is the SAME mechanical
     recipe -- drop the leading [gname], thread a trailing [(b : bool)]
     through [sie_cap_gpr]/[cpu_own], wrap every [Hcont]-shaped
     continuation in [wp_next b (fun CID => ...)], give each lemma its
     OWN implicit `{GEN : GenId} `{CID : CpuId}` binder (they apply each other at a
     hart a [wp_next] crossing may have moved to), delete the two
     now-provably-vacuous premises every one of these lemmas carried
     ([Mf !!! Regidx 4 = mm !!! Regidx 4] and [mm !!! Regidx 4 =
     cid_word] -- callee_saved's tp conjunct is gone, so both are dead
     weight, exactly as in wp_walk_epilogue_sconf/wp_walk_tail_sconf
     above), and at every leaf application: drop [γ], append [b], turn
     the old [rd <> csp_rs1]-shaped discriminate into [ltac:(rdok)], and
     bridge every leaf whose OWN written value reads the entry map via
     [rget] (cmv/addi4/cadd/caddi/cslli/srai/addw/srli/ori, and any
     leaf's address/value premise built from one of THEIR outputs) back
     down to the [!!!]-spelled form with [iEval (rgne) in "Hcg"] (two
     [rgne]s back-to-back for a leaf that reads two registers) --
     WITHOUT this bridge, the [!!!]-spelled [set] two or three
     instructions later silently fails to fold against the leaf's real
     (still-[rget]-laden) postcondition, and the NEXT leaf's [iApply]
     hangs for effectively-ever trying to unify a [rget] chain nested
     three or more deep (reproduced and root-caused during this port:
     confirmed via [Timeout 20] to be a genuine non-termination, not
     merely slow, and fixed by adding the missing [rgne] bridge -- NOT
     by touching [wp_lui_s_sconf]/any leaf file, which were and remain
     correct).

     wp_walk_loop_sconf did get this treatment because it is
     qualitatively bigger than the five lemmas above it: it is a FUEL
     INDUCTION on [L] needing the porting guide's "two hart binders"
     ([revert CID g Mf cur w] before [induction L], mirroring
     ProofProcMapstacks.v's validated pattern) threaded through TWO
     top-level branches (descend into an existing kid / allocate under
     an empty slot), each further split on [L' = 0] (exit via
     wp_walk_tail_sconf) vs [L' = 1] (recurse via [IH], needing
     [wp_next_shift] to re-anchor the loop's OWN continuation before
     the recursive call, exactly as ProofProcMapstacks.v's loop does
     for its own IH) vs impossible, PLUS a call into the just-converted
     wp_walk_alloc_sconf (itself carrying two wp_next-wrapped
     continuations, "Hok"/"Hfail", now correctly converted above)
     success continuation's OWN bound page-table-pointer variable is
     ALSO named literally "b" in the pre-port source -- a genuine
     collision with the new SIE-index "b" that has to be renamed
     throughout that whole branch (not merely at the binder, per the
     naming-collision gotcha), on top of ~15 more leaf conversions
     (two caddiw's, two bne's, the probe call, the alloc call) each
     needing the same b-threading + rdok + rgne treatment as above.
     wp_walk_sconf (the top-level entry, calling this loop twice)
     an analogous ~20-leaf prologue and was, in turn, left untouched
     pending the loop.

     This is NOT a design-level blocker the way ProofKvminithart.v's is
     (no missing central transport lemma; the SAME mechanical recipe
     validated five times above applies here too, including a validated
     TWO-hart-binder loop pattern from ProofProcMapstacks.v to follow) --
     it is a real but externally-boxed TIME limit on this porting pass.
     The two lemmas below are reproduced VERBATIM from the pre-port
     source (git rev 136ac81), not modified, so [coqc] on this file
     fails at wp_walk_loop_sconf's first now-mismatched premise/leaf
     call rather than silently passing on an incorrect proof. *)
  (* ============================================================= *)

  Lemma wp_walk_loop_sconf `{GEN : GenId} `{CID : CpuId} (γa : gname)
      (mm Mf : regfile) (t cur : ptree) (L : nat) (w : mword 64) (K : nat) (lvl : nat)
      (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (g : nat) (b : bool) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (* kalloc's transient noff increment stays in int range *)
    (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
    (22 <= K)%nat ->
    uint va < 274877906944 ->
    (1 <= L <= 2)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 19 : mword 5) = va ->
    Mf !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (12 + 9 * Z.of_nat L) ->
    Mf !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int 12 ->
    Mf !!! Regidx (mword_of_int 9 : mword 5)
      = zero_extend' 64 (concat_vec (pt_base cur) (zeros' 12 : mword 12)) ->
    eq_vec (Mf !!! Regidx (mword_of_int 22 : mword 5)) zero_reg = false ->
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    (ptree_maps_lvl L cur vpn w \/ ptree_blocks0_lvl L cur vpn) ->
    (g + grafts_lvl L cur vpn = pt_missing t vpn 1)%nat ->
    sie_cap_gpr Mf (K - 8)%nat b p -∗ cpu_own lvl eb p C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.walk + 0x26)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    ptree_own L (DfracOwn 1) cur -∗
    (∀ (curf : ptree) (d : nat),
       ptree_own L (DfracOwn 1) curf -∗
       ⌜ptree_same_rep0_lvl L cur curf⌝ -∗
       ⌜pt_nodes_lvl L curf = (pt_nodes_lvl L cur + d)%nat⌝ -∗
       ⌜ptree_offpath_eq_lvl L vpn cur curf⌝ -∗
       ⌜pt_present_mono_lvl L cur curf⌝ -∗
       (∃ tf : ptree,
          ptree_own 2 (DfracOwn 1) tf ∗
          ⌜ptree_same_rep0 t tf⌝ ∗
          ⌜pt_nodes tf = (pt_nodes t + g + d)%nat⌝ ∗
          ⌜forall leaf : ptree,
             ptree_leaf_lvl L curf vpn leaf -> ptree_leaf_lvl 2 tf vpn leaf⌝ ∗
          ⌜ptree_offpath_eq vpn t tf⌝ ∗
          ⌜pt_present_mono t tf⌝)) -∗
    kalloc_env γa (avail_sub on g) -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g : nat),
      sie_cap_gpr mr K b p -∗ cpu_own lvl eb p C b -∗
      pc_is ret_tgt -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗
      kalloc_env γa (avail_sub on g) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ptree_same_rep0 t t'⌝ -∗
      ⌜ptree_offpath_eq vpn t t'⌝ -∗
      ⌜pt_present_mono t t'⌝ -∗
      ⌜(g <= pt_missing t vpn 1)%nat⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0
           /\ avail_zero (avail_sub on g))
        \/ (exists p2 p1 w0,
             ptree_level0 t' vpn p2 p1 w0 /\
             mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros va vpn sp0 spr ret_tgt Hlvl HK Hva.
    revert CID g Mf cur w.
    induction L as [| L' IH]; intros CID g Mf cur w HL Hsp Hs3 Hs4 Hs5 Hs1 Hs6 Hx23 Hx24 Hx25 Hx26 Hx27 Hverdict Hgrafts.
    { exfalso; lia. }
    iIntros "Hcg Hcnt #Htext Hpc Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hown Hrestore Henv Hcont".
    iPoseProof (wi_3a with "Htext") as "Hi3a".
    iPoseProof (wi_3c with "Htext") as "Hi3c".
    iPoseProof (wi_3e with "Htext") as "Hi3e".
    iPoseProof (wi_40 with "Htext") as "Hi40".
    iPoseProof (wi_42 with "Htext") as "Hi42".
    (* the slot cell is owned PHYSICALLY ([↦ₚ₈]); the S-mode load reads it
       THROUGH translation, so convert to the VA-tier [↦₈] via the node's own
       claim (uniform-claims), and convert back for the read-only wand. *)
    iDestruct (ptree_own_node_claim L' (DfracOwn 1) cur with "Hown") as "[#Hcurcl Hown]".
    iDestruct (ptree_own_cell_ro L' (DfracOwn 1) cur (vpn_idx (S L') vpn) with "Hown") as "[Hslot Hcl]".
    iDestruct (pt_slot_phys_to_mem (pt_base cur) (vpn_idx (S L') vpn) (DfracOwn 1)
                 (pt_ents cur (vpn_idx (S L') vpn)) with "Hcurcl Hslot") as "Hslot".
    iApply (wp_walk_probe_sconf Mf (K - 8)%nat va (mword_of_int (12 + 9 * Z.of_nat (S L')))
              (u_pte_addr (pt_base cur) (vpn_idx (S L') vpn)) (pt_ents cur (vpn_idx (S L') vpn)) b p
              (dqm:=DfracOwn 1)
              Hs3 Hs4
              ltac:(rewrite Hs1; exact (walk_slot_addr_lvl (S L') (pt_base cur) va ltac:(lia) Hva))
              with "Hcg Htext Hpc Hslot [-]").
    iIntros (CIDb1 Hsb1) "Hcg Hpc Hslot".
    iDestruct (pt_slot_mem_to_phys (pt_base cur) (vpn_idx (S L') vpn) (DfracOwn 1)
                 (pt_ents cur (vpn_idx (S L') vpn)) with "Hcurcl Hslot") as "Hslot".
    iDestruct ("Hcl" with "Hslot") as "Hown".
    set (pte := pt_ents cur (vpn_idx (S L') vpn)).
    set (M4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (u_pte_addr (pt_base cur) (vpn_idx (S L') vpn))]> Mf).
    set (M5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg pte]> M4).
    set (M6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (and_vec pte (sign_extend' 64 (mword_of_int 1 : mword 12)))]> M5).
    assert (HM6a5 : M6 !!! Regidx (mword_of_int 15 : mword 5) = and_vec pte (sign_extend' 64 (mword_of_int 1 : mword 12))) by (rewrite /M6 upd_eq; reflexivity).
    assert (HM6s1 : M6 !!! Regidx (mword_of_int 9 : mword 5) = pte).
    { rewrite /M6. rewrite upd_ne; [| reg_neq]. rewrite /M5 upd_eq. reflexivity. }
    destruct (pt_kids cur (vpn_idx (S L') vpn)) as [c|] eqn:Hkids.
    - (* ===================== V=1: descend into kid c ==================== *)
      assert (Hdesc : pte_valid pte /\ pte_ptr pte /\ u_next_base pte = pt_base c
                      /\ (ptree_maps_lvl L' c vpn w \/ ptree_blocks0_lvl L' c vpn)).
      { unfold pte. destruct Hverdict as [Hm | Hb].
        - destruct Hm as (c' & Hk' & Hv' & Hp' & Hu' & Hmc).
          rewrite Hkids in Hk'. assert (c' = c) by congruence. subst c'.
          split; [exact Hv'| split; [exact Hp'| split; [exact Hu'| left; exact Hmc]]].
        - destruct Hb as [(Hkn & _) | (c' & Hk' & Hv' & Hp' & Hu' & Hbc)].
          + rewrite Hkids in Hkn; discriminate.
          + rewrite Hkids in Hk'. assert (c' = c) by congruence. subst c'.
            split; [exact Hv'| split; [exact Hp'| split; [exact Hu'| right; exact Hbc]]]. }
      destruct Hdesc as (Hv & Hp & Hu & Hnv).
      assert (Hvbit : Z.testbit (bv_unsigned pte) 0 = true).
      { destruct (Z.testbit (bv_unsigned pte) 0) eqn:E; [reflexivity | exfalso].
        exact (pte_valid_invalid_excl pte Hv (pte_invalid_bit0 _ E)). }
      (* +0x3a c.beqz a5 FALLS *)
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.walk + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                M6 (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HM6a5 walk_vbit_eq Hvbit; reflexivity)
                with "Hcg Hpc Hi3a [-]").
      iIntros (CIDb2 Hsb2) "Hcg Hpc".
      assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.walk + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      (* +0x3c c.srli s1,10 *)
      iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.walk + 0x3c)) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
                M6 (K - 8)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3c [-]").
      iIntros (CIDb3 Hsb3) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (M7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (shift_bits_right (M6 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> M6).
      assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.walk + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      (* +0x3e c.slli s1,12 *)
      iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.walk + 0x3e)) (Regidx (mword_of_int 9 : mword 5)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
                M7 (K - 8)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3e [-]").
      iIntros (CIDb4 Hsb4) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (M8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (shift_bits_left (M7 !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> M7).
      assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.walk + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      assert (HM8s1 : M8 !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec (pt_base c) (zeros' 12 : mword 12))).
      { rewrite /M8 upd_eq /M7 upd_eq HM6s1.
        rewrite (walk_descend_base pte Hv Hp). rewrite Hu. reflexivity. }
      (* descend the ownership; extend the restore *)
      iDestruct (ptree_own_descend L' (DfracOwn 1) cur c (vpn_idx (S L') vpn) Hkids with "Hown") as "[Hownc Hframe]".
      iAssert (∀ (curf : ptree) (d : nat), ptree_own L' (DfracOwn 1) curf -∗ ⌜ptree_same_rep0_lvl L' c curf⌝ -∗
                 ⌜pt_nodes_lvl L' curf = (pt_nodes_lvl L' c + d)%nat⌝ -∗
                 ⌜ptree_offpath_eq_lvl L' vpn c curf⌝ -∗
                 ⌜pt_present_mono_lvl L' c curf⌝ -∗
                 (∃ tf : ptree, ptree_own 2 (DfracOwn 1) tf ∗ ⌜ptree_same_rep0 t tf⌝ ∗
                    ⌜pt_nodes tf = (pt_nodes t + g + d)%nat⌝ ∗
                    ⌜forall leaf, ptree_leaf_lvl L' curf vpn leaf -> ptree_leaf_lvl 2 tf vpn leaf⌝ ∗
                    ⌜ptree_offpath_eq vpn t tf⌝ ∗
                    ⌜pt_present_mono t tf⌝))%I
        with "[Hframe Hrestore]" as "Hrestore'".
      { iIntros (curf d) "Hownf %Hsr %Hd %Hoffc %Hpresc".
        iDestruct ("Hframe" $! curf with "Hownf") as "Hup".
        iDestruct ("Hrestore" $! (pt_upd_kid cur (vpn_idx (S L') vpn) (Some curf)) d with "Hup [%] [%] [%] [%]") as (tf) "(Htf & %Hsame & %Hnd & %Hleaf & %Hoff & %Hpres)".
        { exact (ptree_same_rep0_lvl_upd_kid L' cur (vpn_idx (S L') vpn) c curf Hkids Hsr). }
        { pose proof (pt_nodes_lvl_kids_upd L' cur (vpn_idx (S L') vpn) (Some curf)) as Hm.
          rewrite Hkids in Hm. cbn [pt_kid_nodes] in Hm. lia. }
        { exact (ptree_offpath_eq_lvl_upd_kid L' vpn cur curf c ltac:(lia) Hkids Hoffc). }
        { exact (pt_present_mono_lvl_upd_kid L' vpn cur curf c ltac:(lia) Hkids Hpresc). }
        iExists tf. iFrame "Htf". iSplit; [done|]. iSplit; [iPureIntro; exact Hnd|]. iSplit; [| iSplit; [iPureIntro; exact Hoff | iPureIntro; exact Hpres]]. iPureIntro. intros leaf Hlf.
        apply Hleaf.
        assert (Hbcf : u_next_base pte = pt_base curf).
        { destruct Hsr as (Hbc & _ & _). rewrite Hu. symmetry. exact Hbc. }
        exact (ptree_leaf_lvl_upd_kid_intro L' cur (vpn_idx (S L') vpn) curf leaf vpn eq_refl Hv Hp Hbcf Hlf). }
      (* +0x40 c.addiw s4,-9 *)
      iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.walk + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                M8 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi40 [-]").
      iIntros (CIDb5 Hsb5) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (M9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (M8 !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> M8).
      assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.walk + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HM8s4 : M8 !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (12 + 9 * Z.of_nat (S L'))).
      { rewrite /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hs4. }
      assert (HM9s4 : M9 !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (12 + 9 * Z.of_nat L')).
      { rewrite /M9 upd_eq HM8s4. exact (walk_caddiw_dec9 L' HL). }
      assert (HM9s5 : M9 !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int 12).
      { rewrite /M9. rewrite upd_ne; [| reg_neq]. rewrite /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hs5. }
      assert (HM9s3 : M9 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hs3. }
      assert (HM9s1 : M9 !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec (pt_base c) (zeros' 12 : mword 12))).
      { rewrite /M9. rewrite upd_ne; [| reg_neq]. exact HM8s1. }
      assert (HspM9 : M9 !!! Regidx csp_rs1 = spr).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hsp. }
      assert (HM9s6 : eq_vec (M9 !!! Regidx (mword_of_int 22 : mword 5)) zero_reg = false).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hs6. }
      assert (HM9x23 : M9 !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23)).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hx23. }
      assert (HM9x24 : M9 !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hx24. }
      assert (HM9x25 : M9 !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hx25. }
      assert (HM9x26 : M9 !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hx26. }
      assert (HM9x27 : M9 !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hx27. }
      destruct L' as [| [| k]].
      + (* L'=0: bne FALLS, exit to the tail at +0x46 *)
        iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.walk + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                  M9 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; rewrite HM9s4 HM9s5; vm_compute; reflexivity)
                  with "Hcg Hpc Hi42 [-]").
        iIntros (CIDb6 Hsb6) "Hcg Hpc".
        assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.walk + 0x42) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp46) in "Hpc".
        iDestruct ("Hrestore'" $! c 0%nat with "Hownc [%] [%] [%] [%]") as (tf) "(Htf & %Hsame & %Hnd & %Hleaf & %Hoff & %Hpres)".
        { apply ptree_same_rep0_lvl_refl. }
        { lia. }
        { apply ptree_offpath_eq_lvl_refl. }
        { apply pt_present_mono_lvl_refl. }
        assert (Hmiss : (g <= pt_missing t vpn 1)%nat).
        { pose proof Hgrafts as HG. rewrite (grafts_lvl_descend 0 cur c vpn Hkids) in HG.
          cbn [grafts_lvl] in HG. lia. }
        assert (Hl2 : ptree_leaf_lvl 2 tf vpn c) by (apply Hleaf; reflexivity).
        destruct (ptree_leaf_lvl_2 tf vpn c Hl2) as (p2 & p1 & Hl0tf & Hunb).
        (* [Hcont]/[Hcnt] entered this ITERATION at [CID]; the six plain
           instructions above (probe's own crossing plus cbeqz/csrli/cslli/
           caddiw/bne) landed on [CIDb6] -- re-anchor both once. *)
        assert (Hchainb1 : b = false \/ p = zero_reg -> (CIDb6 : CPU) = (CID : CPU)) by wp_next_chain.
        iDestruct (wp_next_shift Hchainb1 with "Hcont") as "Hcont".
        iDestruct (cpu_own_transport CID CIDb6 lvl eb p C b Hchainb1 with "Hcnt") as "Hcnt".
        iApply (wp_walk_tail_sconf γa mm M9 t tf (pt_base c) K lvl eb p C on g b HK Hva
                  HspM9 HM9s3 HM9s1 HM9x23 HM9x24 HM9x25 HM9x26 HM9x27 Hsame Hoff Hpres ltac:(lia) Hmiss
                  ltac:(exists p2, p1, (pt_ents c (vpn_idx 0 vpn)); split;
                        [exact Hl0tf | unfold pt_addr0; rewrite Hunb; reflexivity])
                  with "Hcg Hcnt Htext Hpc Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Htf Henv Hcont").
      + (* L'=1: bne TAKEN, loop back to +0x26 via the IH *)
        iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.walk + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                  M9 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; rewrite HM9s4 HM9s5; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi42 [-]").
        iIntros (CIDb6' Hsb6'). iNext. iIntros "Hcg Hpc".
        assert (Hbk26 : add_vec (mword_of_int (KernelSyms.walk + 0x42) : mword 64) (sign_extend' 64 (mword_of_int 8164 : mword 13)) = mword_of_int (KernelSyms.walk + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hbk26) in "Hpc".
        assert (Hchainb2 : b = false \/ p = zero_reg -> (CIDb6' : CPU) = (CID : CPU)) by wp_next_chain.
        iDestruct (wp_next_shift Hchainb2 with "Hcont") as "Hcont".
        iDestruct (cpu_own_transport CID CIDb6' lvl eb p C b Hchainb2 with "Hcnt") as "Hcnt".
        iApply (IH CIDb6' g M9 c w ltac:(lia) HspM9 HM9s3 HM9s4 HM9s5 HM9s1 HM9s6 HM9x23 HM9x24 HM9x25 HM9x26 HM9x27 Hnv
                  ltac:(rewrite <- (grafts_lvl_descend 1 cur c vpn Hkids); exact Hgrafts)
                  with "Hcg Hcnt Htext Hpc Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hownc Hrestore' Henv Hcont").
      + exfalso; lia.
    - (* ===================== V=0: allocate under the empty slot ========= *)
      assert (Hez : pte = mword_of_int 0).
      { unfold pte. destruct Hverdict as [Hm | Hb].
        - destruct Hm as (c' & Hk' & _). rewrite Hkids in Hk'; discriminate.
        - destruct Hb as [(_ & Hz) | (c' & Hk' & _)].
          + exact Hz.
          + rewrite Hkids in Hk'; discriminate. }
      assert (Hvbit0 : Z.testbit (bv_unsigned pte) 0 = false).
      { rewrite Hez. replace (bv_unsigned (mword_of_int 0 : mword 64)) with 0 by (vm_compute; reflexivity). apply Z.bits_0. }
      assert (HM6s18 : M6 !!! Regidx (mword_of_int 18 : mword 5) = u_pte_addr (pt_base cur) (vpn_idx (S L') vpn)).
      { rewrite /M6. rewrite upd_ne; [| reg_neq]. rewrite /M5. rewrite upd_ne; [| reg_neq]. rewrite /M4 upd_eq. reflexivity. }
      assert (HspM6 : M6 !!! Regidx csp_rs1 = spr).
      { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hsp. }
      assert (HM6s6 : eq_vec (M6 !!! Regidx (mword_of_int 22 : mword 5)) zero_reg = false).
      { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hs6. }
      assert (HM6x23 : M6 !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23)).
      { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hx23. }
      assert (HM6x24 : M6 !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)).
      { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hx24. }
      assert (HM6x25 : M6 !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
      { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hx25. }
      assert (HM6x26 : M6 !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
      { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hx26. }
      assert (HM6x27 : M6 !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
      { rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hx27. }
      (* +0x3a c.beqz a5 TAKEN -> +0x72 *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.walk + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                M6 (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HM6a5 walk_vbit_eq Hvbit0; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3a [-]").
      iIntros (CIDc0 Hsc0). iNext. iIntros "Hcg Hpc".
      assert (Htgt72 : add_vec (mword_of_int (KernelSyms.walk + 0x3a) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")))) = mword_of_int (KernelSyms.walk + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt72) in "Hpc".
      iCombine "Hrestore Hcont" as "HF".
      (* the graft accessor delivers VA-tier ([↦₈]) cells: the walk stores the
         pointer PTE THROUGH translation, so wrap [ptree_own_graft]'s physical
         cells with the node's own claim (uniform-claims PHYSICAL TIER). *)
      assert (Hgraft8 : ptree_own (S L') (DfracOwn 1) cur ⊢
         u_pte_addr (pt_base cur) (vpn_idx (S L') vpn) ↦₈{DfracOwn 1} pte ∗
         (∀ bg : mword 44,
            u_pte_addr (pt_base cur) (vpn_idx (S L') vpn) ↦₈{DfracOwn 1} pt_ptr_pte bg -∗
            ptree_own L' (DfracOwn 1) (pt_empty_node bg) -∗
            ptree_own (S L') (DfracOwn 1) (pt_graft cur (vpn_idx (S L') vpn) bg))).
      { iIntros "Hown0".
        iDestruct (ptree_own_node_claim L' (DfracOwn 1) cur with "Hown0") as "[#Hcl0 Hown0]".
        iDestruct (ptree_own_graft L' (DfracOwn 1) cur (vpn_idx (S L') vpn) Hkids with "Hown0")
          as "[Hcell Hgw]".
        iDestruct (pt_slot_phys_to_mem (pt_base cur) (vpn_idx (S L') vpn) (DfracOwn 1) pte
                     with "Hcl0 Hcell") as "Hcell".
        iSplitL "Hcell"; [iExact "Hcell" |].
        iIntros (bg) "Hcell Hchild".
        iDestruct (pt_slot_mem_to_phys (pt_base cur) (vpn_idx (S L') vpn) (DfracOwn 1) (pt_ptr_pte bg)
                     with "Hcl0 Hcell") as "Hcell".
        iApply ("Hgw" $! bg with "Hcell Hchild"). }
      (* [Hcont]/[Hcnt] entered this iteration at [CID]; cbeqz.taken landed
         on [CIDc0] -- re-anchor once before feeding [wp_walk_alloc_sconf]. *)
      assert (Hchainc0 : b = false \/ p = zero_reg -> (CIDc0 : CPU) = (CID : CPU)) by wp_next_chain.
      iDestruct (cpu_own_transport CID CIDc0 lvl eb p C b Hchainc0 with "Hcnt") as "Hcnt".
      iApply (wp_walk_alloc_sconf γa mm M6 cur
                (fun bg => pt_graft cur (vpn_idx (S L') vpn) bg) (S L') L'
                (u_pte_addr (pt_base cur) (vpn_idx (S L') vpn)) pte K lvl eb p C _ on g b Hlvl HK
                HspM6 HM6s18 HM6s6 HM6x23 HM6x24 HM6x25 HM6x26 HM6x27
                Hgraft8
                with "Hcg Hcnt Htext Hpc Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hown Henv HF").
      + (* ---- Hok: kalloc succeeded; continue the loop with the grafted subtree ---- *)
        iIntros (CIDok Hsok Mo bn) "%Hcs %Hb9 Hcg Hcnt Hpc Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hownb Henv HF".
        iDestruct "HF" as "[Hrestore Hcont]".
        iDestruct (ptree_own_descend L' (DfracOwn 1) (pt_graft cur (vpn_idx (S L') vpn) bn) (pt_empty_node bn) (vpn_idx (S L') vpn) (pt_graft_kid cur (vpn_idx (S L') vpn) bn) with "Hownb") as "[Hownc Hframe]".
        iAssert (∀ (curf : ptree) (d : nat), ptree_own L' (DfracOwn 1) curf -∗ ⌜ptree_same_rep0_lvl L' (pt_empty_node bn) curf⌝ -∗
                   ⌜pt_nodes_lvl L' curf = (pt_nodes_lvl L' (pt_empty_node bn) + d)%nat⌝ -∗
                   ⌜ptree_offpath_eq_lvl L' vpn (pt_empty_node bn) curf⌝ -∗
                   ⌜pt_present_mono_lvl L' (pt_empty_node bn) curf⌝ -∗
                   (∃ tf : ptree, ptree_own 2 (DfracOwn 1) tf ∗ ⌜ptree_same_rep0 t tf⌝ ∗
                      ⌜pt_nodes tf = (pt_nodes t + S g + d)%nat⌝ ∗
                      ⌜forall leaf, ptree_leaf_lvl L' curf vpn leaf -> ptree_leaf_lvl 2 tf vpn leaf⌝ ∗
                      ⌜ptree_offpath_eq vpn t tf⌝ ∗
                      ⌜pt_present_mono t tf⌝))%I
          with "[Hframe Hrestore]" as "Hrestore'".
        { iIntros (curf d) "Hownf %Hsr %Hd %Hoffc %Hpresc".
          iDestruct ("Hframe" $! curf with "Hownf") as "Hup".
          iDestruct ("Hrestore" $! (pt_upd_kid (pt_graft cur (vpn_idx (S L') vpn) bn) (vpn_idx (S L') vpn) (Some curf)) (1 + d)%nat with "Hup [%] [%] [%] [%]") as (tf) "(Htf & %Hsame & %Hnd & %Hleaf & %Hoff & %Hpres)".
          { eapply ptree_same_rep0_lvl_trans.
            - exact (ptree_same_rep0_lvl_graft L' cur (vpn_idx (S L') vpn) bn Hkids Hez).
            - exact (ptree_same_rep0_lvl_upd_kid L' (pt_graft cur (vpn_idx (S L') vpn) bn) (vpn_idx (S L') vpn) (pt_empty_node bn) curf (pt_graft_kid cur (vpn_idx (S L') vpn) bn) Hsr). }
          { pose proof (pt_nodes_lvl_kids_upd L' (pt_graft cur (vpn_idx (S L') vpn) bn) (vpn_idx (S L') vpn) (Some curf)) as Hm.
            rewrite (pt_graft_kid cur (vpn_idx (S L') vpn) bn) in Hm. cbn [pt_kid_nodes] in Hm.
            rewrite (pt_nodes_lvl_graft L' cur (vpn_idx (S L') vpn) bn Hkids) in Hm. lia. }
          { exact (ptree_offpath_eq_lvl_graft L' vpn cur curf bn ltac:(lia) Hkids Hoffc). }
          { exact (pt_present_mono_lvl_graft L' vpn cur curf bn ltac:(lia) Hkids Hpresc). }
          iExists tf. iFrame "Htf". iSplit; [done|]. iSplit; [iPureIntro; lia|]. iSplit; [| iSplit; [iPureIntro; exact Hoff | iPureIntro; exact Hpres]]. iPureIntro. intros leaf Hlf.
          apply Hleaf.
          assert (Hbcf : u_next_base (pt_ents (pt_graft cur (vpn_idx (S L') vpn) bn) (vpn_idx (S L') vpn)) = pt_base curf).
          { rewrite pt_graft_ent pt_ptr_pte_base. destruct Hsr as (Hbc & _ & _). rewrite Hbc pt_empty_node_base. reflexivity. }
          exact (ptree_leaf_lvl_upd_kid_intro L' (pt_graft cur (vpn_idx (S L') vpn) bn) (vpn_idx (S L') vpn) curf leaf vpn eq_refl
                   ltac:(rewrite pt_graft_ent; exact (pt_ptr_pte_valid bn))
                   ltac:(rewrite pt_graft_ent; exact (pt_ptr_pte_ptr bn))
                   Hbcf Hlf). }
        set (Rb := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (Mo !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> Mo).
        assert (HMos4 : Mo !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (12 + 9 * Z.of_nat (S L'))).
        { rewrite (Hcs (mword_of_int 20) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
          rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hs4. }
        assert (HMos5 : Mo !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int 12).
        { rewrite (Hcs (mword_of_int 21) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
          rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hs5. }
        iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.walk + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                  Mo (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi40 [-]").
        iIntros (CIDc1 Hsc1) "Hcg Hpc". iEval (rgne) in "Hcg".
        assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.walk + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp42) in "Hpc".
        assert (HRbs4 : Rb !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (12 + 9 * Z.of_nat L')).
        { rewrite /Rb upd_eq HMos4. exact (walk_caddiw_dec9 L' HL). }
        assert (HRbs5 : Rb !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int 12).
        { rewrite /Rb. rewrite upd_ne; [| reg_neq]. exact HMos5. }
        assert (HRbs3 : Rb !!! Regidx (mword_of_int 19 : mword 5) = va).
        { rewrite /Rb. rewrite upd_ne; [| reg_neq].
          rewrite (Hcs (mword_of_int 19) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
          rewrite /M6 /M5 /M4. repeat (rewrite upd_ne; [| reg_neq]). exact Hs3. }
        assert (HRbs1 : Rb !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec (pt_base (pt_empty_node bn)) (zeros' 12 : mword 12))).
        { rewrite /Rb. rewrite upd_ne; [| reg_neq]. rewrite pt_empty_node_base. exact Hb9. }
        assert (HspRb : Rb !!! Regidx csp_rs1 = spr).
        { rewrite /Rb. rewrite upd_ne; [| reg_neq].
          rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). exact HspM6. }
        assert (HRbs6 : eq_vec (Rb !!! Regidx (mword_of_int 22 : mword 5)) zero_reg = false).
        { rewrite /Rb. rewrite upd_ne; [| reg_neq].
          rewrite (Hcs (mword_of_int 22) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). exact HM6s6. }
        assert (HRbx23 : Rb !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23)).
        { rewrite /Rb. rewrite upd_ne; [| reg_neq].
          rewrite (Hcs (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). exact HM6x23. }
        assert (HRbx24 : Rb !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)).
        { rewrite /Rb. rewrite upd_ne; [| reg_neq].
          rewrite (Hcs (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). exact HM6x24. }
        assert (HRbx25 : Rb !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
        { rewrite /Rb. rewrite upd_ne; [| reg_neq].
          rewrite (Hcs (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). exact HM6x25. }
        assert (HRbx26 : Rb !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
        { rewrite /Rb. rewrite upd_ne; [| reg_neq].
          rewrite (Hcs (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). exact HM6x26. }
        assert (HRbx27 : Rb !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
        { rewrite /Rb. rewrite upd_ne; [| reg_neq].
          rewrite (Hcs (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). exact HM6x27. }
        destruct L' as [| [| k]].
        * (* L'=0: bne FALLS to the tail *)
          iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.walk + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                    Rb (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rgne; rgne; rewrite HRbs4 HRbs5; vm_compute; reflexivity)
                    with "Hcg Hpc Hi42 [-]").
          iIntros (CIDc2 Hsc2) "Hcg Hpc".
          assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.walk + 0x42) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp46) in "Hpc".
          iDestruct ("Hrestore'" $! (pt_empty_node bn) 0%nat with "Hownc [%] [%] [%] [%]") as (tf) "(Htf & %Hsame & %Hnd & %Hleaf & %Hoff & %Hpres)".
          { apply ptree_same_rep0_lvl_refl. }
          { lia. }
          { apply ptree_offpath_eq_lvl_refl. }
          { apply pt_present_mono_lvl_refl. }
          assert (Hmiss : (S g <= pt_missing t vpn 1)%nat).
          { pose proof Hgrafts as HG. rewrite (grafts_lvl_none 0 cur vpn Hkids) in HG. lia. }
          assert (Hl2 : ptree_leaf_lvl 2 tf vpn (pt_empty_node bn)) by (apply Hleaf; reflexivity).
          destruct (ptree_leaf_lvl_2 tf vpn (pt_empty_node bn) Hl2) as (p2 & p1 & Hl0tf & Hunb).
          (* [Hcnt] was refreshed at [CIDok] by alloc's own "Hok"; [Hcont]
             rode through alloc UNTOUCHED inside the opaque [F], so it is
             STILL anchored at [CID].  caddiw+bne landed on [CIDc2]. *)
          assert (Hchainc1 : b = false \/ p = zero_reg -> (CIDc2 : CPU) = (CID : CPU)) by wp_next_chain.
          iDestruct (wp_next_shift Hchainc1 with "Hcont") as "Hcont".
          assert (Hchainc1' : b = false \/ p = zero_reg -> (CIDc2 : CPU) = (CIDok : CPU)) by wp_next_chain.
          iDestruct (cpu_own_transport CIDok CIDc2 lvl eb p C b Hchainc1' with "Hcnt") as "Hcnt".
          iApply (wp_walk_tail_sconf γa mm Rb t tf (pt_base (pt_empty_node bn)) K lvl eb p C on (S g) b HK Hva
                    HspRb HRbs3 HRbs1 HRbx23 HRbx24 HRbx25 HRbx26 HRbx27 Hsame Hoff Hpres ltac:(lia) Hmiss
                    ltac:(exists p2, p1, (pt_ents (pt_empty_node bn) (vpn_idx 0 vpn)); split;
                          [exact Hl0tf | unfold pt_addr0; rewrite Hunb; reflexivity])
                    with "Hcg Hcnt Htext Hpc Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Htf Henv Hcont").
        * (* L'=1: bne TAKEN, loop via IH *)
          iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.walk + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                    Rb (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rgne; rgne; rewrite HRbs4 HRbs5; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi42 [-]").
          iIntros (CIDc2' Hsc2'). iNext. iIntros "Hcg Hpc".
          assert (Hbk26 : add_vec (mword_of_int (KernelSyms.walk + 0x42) : mword 64) (sign_extend' 64 (mword_of_int 8164 : mword 13)) = mword_of_int (KernelSyms.walk + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hbk26) in "Hpc".
          assert (Hchainc2 : b = false \/ p = zero_reg -> (CIDc2' : CPU) = (CID : CPU)) by wp_next_chain.
          iDestruct (wp_next_shift Hchainc2 with "Hcont") as "Hcont".
          assert (Hchainc2' : b = false \/ p = zero_reg -> (CIDc2' : CPU) = (CIDok : CPU)) by wp_next_chain.
          iDestruct (cpu_own_transport CIDok CIDc2' lvl eb p C b Hchainc2' with "Hcnt") as "Hcnt".
          iApply (IH CIDc2' (S g) Rb (pt_empty_node bn) w ltac:(lia) HspRb HRbs3 HRbs4 HRbs5 HRbs1 HRbs6 HRbx23 HRbx24 HRbx25 HRbx26 HRbx27
                    (or_intror (ptree_blocks0_lvl_empty _ bn vpn))
                    ltac:(rewrite (grafts_lvl_empty 1 bn vpn);
                          pose proof Hgrafts as HG; rewrite (grafts_lvl_none 1 cur vpn Hkids) in HG; lia)
                    with "Hcg Hcnt Htext Hpc Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hownc Hrestore' Henv Hcont").
        * exfalso; lia.
      + (* ---- Hfail: kalloc returned 0; return 0 through the tail's epilogue ---- *)
        iIntros (CIDfl Hsfl Mo) "%Hcs %Ha0 %Havz Hcg Hcnt Hpc Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hown Henv HF".
        iDestruct "HF" as "[Hrestore Hcont]".
        iDestruct ("Hrestore" $! cur 0%nat with "Hown [%] [%] [%] [%]") as (tf) "(Htf & %Hsame & %Hnd & %Hleaf & %Hoff & %Hpres)".
        { apply ptree_same_rep0_lvl_refl. }
        { lia. }
        { apply ptree_offpath_eq_lvl_refl. }
        { apply pt_present_mono_lvl_refl. }
        assert (Hmiss : (g <= pt_missing t vpn 1)%nat).
        { pose proof Hgrafts as HG. rewrite (grafts_lvl_none L' cur vpn Hkids) in HG. lia. }
        (* [Hcont] rode through alloc untouched inside [F], still anchored at
           [CID]; [Hcnt] was already refreshed to [CIDfl] by alloc's own
           "Hfail", so only [Hcont] needs re-anchoring here. *)
        assert (Hchainf : b = false \/ p = zero_reg -> (CIDfl : CPU) = (CID : CPU)) by wp_next_chain.
        iDestruct (wp_next_shift Hchainf with "Hcont") as "Hcont".
        iApply (wp_walk_epilogue_sconf γa mm Mo t tf K lvl eb p C on g b HK
                  ltac:(rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact HspM6)
                  ltac:(rewrite (Hcs (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact HM6x23)
                  ltac:(rewrite (Hcs (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact HM6x24)
                  ltac:(rewrite (Hcs (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact HM6x25)
                  ltac:(rewrite (Hcs (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact HM6x26)
                  ltac:(rewrite (Hcs (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact HM6x27)
                  Hsame Hoff Hpres ltac:(lia) Hmiss
                  ltac:(left; split; [exact Ha0 | exact Havz])
                  with "Hcg Hcnt Htext Hpc Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Htf Henv Hcont").
  Qed.

  Lemma wp_walk_sconf `{GEN : GenId} `{CID : CpuId} (γa : gname)
      (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (K : nat) (lvl : nat)
      (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (b : bool)
    : wp_walk_sconf_body γa mm t m K lvl eb p C on b.
  Proof.
    cbv beta delta [wp_walk_sconf_body].
    intros va vpn ret_tgt Hlvl HK Ha0 Ha2 Hva Hrep Hcid.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> mm).
    assert (Hsp1 : W1 !!! Regidx csp_rs1 = pa_stk (mm !!! Regidx csp_rs1) 8).
    { rewrite /W1 upd_eq. unfold regval_into_reg, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    iIntros "Hcg Hcnt #Htext Hpc Hptree Henv Hcont".
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
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.walk) (mword_of_int 60 : mword 6) mm K 8 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CIDw1 Hsw1) "Hcg Hframe Hpc".
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
    assert (Hpp02 : add_vec_int (mword_of_int KernelSyms.walk : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp x1,56(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x02)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 8)%nat v56 b with "Hcg Hpc Hi02 [Hc56] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc56". }
    iIntros (CIDw2 Hsw2) "Hcg Hpc Hc56". iEval (rgne) in "Hc56".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.walk + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp x8,48(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x04)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 8)%nat v48 b with "Hcg Hpc Hi04 [Hc48] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc48". }
    iIntros (CIDw3 Hsw3) "Hcg Hpc Hc48". iEval (rgne) in "Hc48".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.walk + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp x9,40(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x06)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              W1 (K - 8)%nat v40 b with "Hcg Hpc Hi06 [Hc40] [-]").
    { iEval (rewrite HspW1 Hb3). iExact "Hc40". }
    iIntros (CIDw4 Hsw4) "Hcg Hpc Hc40". iEval (rgne) in "Hc40".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.walk + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp x18,32(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x08)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              W1 (K - 8)%nat v32 b with "Hcg Hpc Hi08 [Hc32] [-]").
    { iEval (rewrite HspW1 Hb4). iExact "Hc32". }
    iIntros (CIDw5 Hsw5) "Hcg Hpc Hc32". iEval (rgne) in "Hc32".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.walk + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp x19,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x0a)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              W1 (K - 8)%nat v24 b with "Hcg Hpc Hi0a [Hc24] [-]").
    { iEval (rewrite HspW1 Hb5). iExact "Hc24". }
    iIntros (CIDw6 Hsw6) "Hcg Hpc Hc24". iEval (rgne) in "Hc24".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.walk + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.sdsp x20,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x0c)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              W1 (K - 8)%nat v16 b with "Hcg Hpc Hi0c [Hc16] [-]").
    { iEval (rewrite HspW1 Hb6). iExact "Hc16". }
    iIntros (CIDw7 Hsw7) "Hcg Hpc Hc16". iEval (rgne) in "Hc16".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.walk + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.sdsp x21,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x0e)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              W1 (K - 8)%nat v08 b with "Hcg Hpc Hi0e [Hc08] [-]").
    { iEval (rewrite HspW1 Hb7). iExact "Hc08". }
    iIntros (CIDw8 Hsw8) "Hcg Hpc Hc08". iEval (rgne) in "Hc08".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.walk + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.sdsp x22,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walk + 0x10)) (mword_of_int 0 : mword 6) (mword_of_int 22 : mword 5)
              W1 (K - 8)%nat v00 b with "Hcg Hpc Hi10 [Hc00] [-]").
    { iEval (rewrite HspW1 Hb8). iExact "Hc00". }
    iIntros (CIDw9 Hsw9) "Hcg Hpc Hc00". iEval (rgne) in "Hc00".
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.walk + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.addi4spn s0,sp,64 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.walk + 0x12)) (Cregidx (mword_of_int 0)) (mword_of_int 16 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [-]").
    iIntros (CIDw10 Hsw10) "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> W1).
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.walk + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.mv x9,x10 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.walk + 0x14)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              W2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CIDw11 Hsw11) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (W3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (W2 !!! Regidx (mword_of_int 10 : mword 5)))]> W2).
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.walk + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 c.mv x19,x11 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.walk + 0x16)) (mword_of_int 19 : mword 5) (mword_of_int 11 : mword 5)
              W3 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CIDw12 Hsw12) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (W4 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg
        (add_vec zero_reg (W3 !!! Regidx (mword_of_int 11 : mword 5)))]> W3).
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.walk + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.mv x22,x12 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.walk + 0x18)) (mword_of_int 22 : mword 5) (mword_of_int 12 : mword 5)
              W4 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CIDw13 Hsw13) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (W5 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg
        (add_vec zero_reg (W4 !!! Regidx (mword_of_int 12 : mword 5)))]> W4).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.walk + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.li a5,-1 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.walk + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 63 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))
              W5 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi1a [-]").
    iIntros (CIDw14 Hsw14) "Hcg Hpc".
    set (W6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> W5).
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.walk + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.srli a5,26 *)
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.walk + 0x1c)) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) (mword_of_int 26 : mword 6)
              W6 (K - 8)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [-]").
    iIntros (CIDw15 Hsw15) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (W7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (W6 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 26 : mword 6) (Z.sub log2_xlen 1) 0))]> W6).
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.walk + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.li s4,30 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.walk + 0x1e)) (mword_of_int 20 : mword 5) (mword_of_int 30 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 30 : mword 6))))
              W7 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi1e [-]").
    iIntros (CIDw16 Hsw16) "Hcg Hpc".
    set (W8 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 30 : mword 6))))]> W7).
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.walk + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 c.li s5,12 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.walk + 0x20)) (mword_of_int 21 : mword 5) (mword_of_int 12 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 12 : mword 6))))
              W8 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi20 [-]").
    iIntros (CIDw17 Hsw17) "Hcg Hpc".
    set (W9 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 12 : mword 6))))]> W8).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.walk + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.walk + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
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
    iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.walk + 0x22)) (mword_of_int 68 : mword 13) (mword_of_int 11 : mword 5) (mword_of_int 15 : mword 5)
              W9 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; rewrite HW9a5 HW9va; unfold zopz0zI_u; apply Z.ltb_ge;
                    replace (uint (mword_of_int 274877906943 : mword 64)) with 274877906943 by (vm_compute; reflexivity);
                    lia)
              with "Hcg Hpc Hi22 [-]").
    iIntros (CIDw18 Hsw18) "Hcg Hpc".
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.walk + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.walk + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
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
    (* ---- funnel into the fuel-generic loop at level 2 ---- *)
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
    assert (HspW9 : W9 !!! Regidx csp_rs1 = spr).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2. repeat (rewrite upd_ne; [| reg_neq]). exact HspW1. }
    assert (HW9s4' : W9 !!! Regidx (mword_of_int 20 : mword 5) = mword_of_int (12 + 9 * Z.of_nat 2)).
    { rewrite HW9s4. apply bv_eq; vm_compute; reflexivity. }
    assert (HW9s5 : W9 !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int 12).
    { rewrite /W9 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HW9s6 : eq_vec (W9 !!! Regidx (mword_of_int 22 : mword 5)) zero_reg = false).
    { rewrite /W9 /W8 /W7 /W6 /W5. repeat (rewrite upd_ne; [| reg_neq]). rewrite upd_eq.
      rewrite /W4 /W3 /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). rewrite Ha2.
      vm_compute; reflexivity. }
    assert (HW9x23 : W9 !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23)).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HW9x24 : W9 !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HW9x25 : W9 !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HW9x26 : W9 !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HW9x27 : W9 !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4 /W3 /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    (* identity restore: at level 2 the fuel-generic relation IS the whole-tree one *)
    iAssert (∀ (curf : ptree) (d : nat), ptree_own 2 (DfracOwn 1) curf -∗ ⌜ptree_same_rep0_lvl 2 t curf⌝ -∗
               ⌜pt_nodes_lvl 2 curf = (pt_nodes_lvl 2 t + d)%nat⌝ -∗
               ⌜ptree_offpath_eq_lvl 2 vpn t curf⌝ -∗
               ⌜pt_present_mono_lvl 2 t curf⌝ -∗
               (∃ tf : ptree, ptree_own 2 (DfracOwn 1) tf ∗ ⌜ptree_same_rep0 t tf⌝ ∗
                  ⌜pt_nodes tf = (pt_nodes t + 0 + d)%nat⌝ ∗
                  ⌜forall leaf, ptree_leaf_lvl 2 curf vpn leaf -> ptree_leaf_lvl 2 tf vpn leaf⌝ ∗
                  ⌜ptree_offpath_eq vpn t tf⌝ ∗
                  ⌜pt_present_mono t tf⌝))%I
      as "Hrestore".
    { iIntros (curf d) "Hown %Hsr %Hd %Hoffc %Hpresc". iExists curf. iFrame "Hown". iPureIntro. split; [|split; [|split; [|split]]].
      - apply ptree_same_rep0_lvl_2. exact Hsr.
      - unfold pt_nodes. lia.
      - intros leaf Hlf. exact Hlf.
      - exact Hoffc.
      - exact Hpresc. }
    (* [Hcont]/[Hcnt] were anchored at THIS lemma's entry hart [CID]; the
       18 plain instructions above (push/8x sdsp/addi4spn/3x mv/3x li/srli/
       bltu) each landed on a fresh generic-[b] hart, ending at [CIDw18] --
       re-anchor both once via the composed chain, shared by both branches
       of the [m !! vpn] case split below. *)
    assert (Hchainw : b = false \/ p = zero_reg -> (CIDw18 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift Hchainw with "Hcont") as "Hcont".
    iDestruct (cpu_own_transport CID CIDw18 lvl eb p C b Hchainw with "Hcnt") as "Hcnt".
    destruct (m !! vpn) as [wv|] eqn:Hmv.
    - destruct (proj1 Hrep vpn wv Hmv) as (p2 & p1 & Hmaps).
      iApply (wp_walk_loop_sconf γa mm W9 t t 2 wv K lvl eb p C on 0%nat b Hlvl HK Hva' ltac:(lia)
                HspW9 HW9s3 HW9s4' HW9s5 HW9s1 HW9s6 HW9x23 HW9x24 HW9x25 HW9x26 HW9x27
                (or_introl (ptree_maps_maps_lvl2 t vpn p2 p1 wv Hmaps))
                ltac:(rewrite Nat.add_0_l; apply grafts_lvl_2_missing)
                with "Hcg Hcnt Htext Hpc Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hptree Hrestore Henv Hcont").
    - iApply (wp_walk_loop_sconf γa mm W9 t t 2 (mword_of_int 0) K lvl eb p C on 0%nat b Hlvl HK Hva' ltac:(lia)
                HspW9 HW9s3 HW9s4' HW9s5 HW9s1 HW9s6 HW9x23 HW9x24 HW9x25 HW9x26 HW9x27
                (or_intror (ptree_blocks0_blocks0_lvl2 t vpn (proj2 Hrep vpn Hmv)))
                ltac:(rewrite Nat.add_0_l; apply grafts_lvl_2_missing)
                with "Hcg Hcnt Htext Hpc Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hptree Hrestore Henv Hcont").
  Qed.

End ProofWalk.

End WalkProof.
