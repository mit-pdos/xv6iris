(* ProofUvmclear.v -- uvmclear() over the SIE-agnostic sconf world.

     // mark a PTE invalid for user access.
     void uvmclear(pagetable_t pagetable, uint64 va)
     { pte_t *pte = walk(pagetable, va, 0);
       if (pte == 0) panic("uvmclear");
       *pte &= ~PTE_U; }

   The SMALLEST function in vm.c: a 2-slot frame around the no-alloc walk,
   then a read-modify-write of the level-0 slot.  Straight line -- there is
   no join, because the ONE branch is dead.  Spec of record: SpecUvmclear.v.

   THE DEAD PANIC ARM.  [P.(ud_um) !! vpn = Some w] makes the exact map
   [m_ad] non-empty at [vpn], which kills WALK_NOALLOC's first disjunct
   ([a0 = 0 /\ m !! vpn = None]).  What is left is that the address the walk
   DID return is not NULL, and that is [ucl_slot_nonzero]: the returned
   address is [u_pte_addr b i] for the node ppn [b] the walk descended into,
   [PtBuild.ptree_own_level0_upd] hands out [pt_node_claim b] whose second
   pure conjunct is [page_valid (page_base b)], and a valid page sits at or
   above [kmem_lo] > 0.  (Without [pt_node_claim] carrying [page_valid] --
   the strengthening the freewalk/uvmfree project made -- "the pointer walk
   returned is not NULL" would not be provable at all.)

   THE RESOURCE DANCE mirrors ProofVmfault / ProofUvmcopy:
   [proc_pt_acc_rep0] opens [proc_pt P] to (tree, exact map, view, wf);
   WALK_NOALLOC runs read-only over the tree; [ptree_own_level0_upd] lends
   the slot and takes back the updated tree; [KptTree.pt_slot_{phys_to_mem,
   mem_to_phys}] bridge the physical slot to the VA tier the S-mode load and
   store go through; and [pt_rep0_insert] / [upt_ad_view_set] /
   [proc_pt_wf_clear_u] / [proc_pt_own_set_same] / [proc_pt_rebuild] close
   the invariant at [uptd_set P vpn (pte_clear_u w)].  The page set does not
   move (same ppn), so the ownership conjunct is literally unchanged. *)
Set Printing Depth 40.
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang.
Require Import RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import HartTp WpNext IntrDefs.
Require Import CalleeSaved StackOwn.
Require Import WpSmodeIntr.
Require Import PageGeom.
Require Import PtAdBits.
Require Import CommonWalk PtTree Pt4kWalk PtBuild KptTree.
Require Import UptTree UserPtTree.
Require Import ProcPtOwn.
Require Import CodeUvmclear.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecWalk.
Require Import SpecUvmclear.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(* §0  Pure helpers.                                                      *)
(* ===================================================================== *)

(* the arithmetic, over plain [Z] (the zify-hook rule) *)
Local Lemma ucl_arith (lo x y : Z) : 0 < lo -> lo <= x -> 0 <= y -> x + y * 8 <> 0.
Proof. lia. Qed.

(* [u_pte_addr] IS [pte_addr_at] (CommonWalk / Pt4kWalk spell the same term) *)
Local Lemma ucl_upte_unsigned (b : mword 44) (i : mword 9) :
  bv_unsigned (u_pte_addr b i) = bv_unsigned b * 4096 + bv_unsigned i * 8.
Proof. exact (pte_addr_at_unsigned b i). Qed.

(* THE PANIC ARM IS DEAD: a slot inside a valid page is not the null pointer. *)
Local Lemma ucl_slot_nonzero (b : mword 44) (i : mword 9) :
  page_valid (page_base b) -> eq_vec (u_pte_addr b i) zero_reg = false.
Proof.
  intros (_ & Hlo & _).
  rewrite uint_unsigned in Hlo. unfold page_base in Hlo.
  rewrite page_base_unsigned in Hlo.
  apply eq_vec_false_iff. intros Heq.
  assert (Hz : bv_unsigned (u_pte_addr b i) = 0)
    by (rewrite Heq; vm_compute; reflexivity).
  rewrite ucl_upte_unsigned in Hz.
  pose proof (bv_unsigned_in_range _ i) as Hi.
  refine (ucl_arith kmem_lo _ _ _ Hlo (proj1 Hi) Hz).
  unfold kmem_lo. lia.
Qed.


(* ===================================================================== *)
(* THE WHOLE FUNCTION.                                                    *)
(* ===================================================================== *)

Module UvmclearProof (WalkNoalloc : WALK_NOALLOC) : UVMCLEAR.

Section ProofUvmclear.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* read the node claim's [page_valid] without consuming it (persistent) *)
  Local Lemma ucl_claim_pv (b : mword 44) :
    pt_node_claim b ⊢ ⌜page_valid (page_base b)⌝.
  Proof. iIntros "(_ & Hpv & _)". iExact "Hpv". Qed.

  Lemma wp_uvmclear_sconf (mm : regfile)
      (P : uptd) (w : mword 64) (K : nat) (b : bool) (p : mword 64)
    : wp_uvmclear_sconf_body mm P w K b p.
  Proof.
    cbv beta delta [wp_uvmclear_sconf_body].
    intros pcE va vpn ret_tgt HK Hroot Hvab Hum Hperm.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    iIntros "Hcg #Htext Hpc Hpt Hcont".
    (* ---- OPEN the user page table ---- *)
    iDestruct (proc_pt_acc_rep0 P with "Hpt") as (t m_ad)
      "(%Hrep & %Hview & %Hbase & %Hwf & Hptree & Hown)".
    assert (Hmapwf : upt_map_wf P.(ud_um)) by exact (proj1 Hwf).
    pose proof (upt_map_wf_not_tramp _ _ _ Hmapwf Hum) as Hntr.
    pose proof (upt_map_wf_not_tf _ _ _ Hmapwf Hum) as Hntf.
    (* the exact map has an entry at [vpn], and it is an A/D variant of [w] *)
    destruct (m_ad !! vpn) as [wr |] eqn:Had.
    2: { exfalso. destruct (proj1 (proj1 Hview vpn) Had) as (_ & _ & Hnn).
         rewrite Hum in Hnn. discriminate. }
    destruct (upt_ad_view_um P.(ud_tfp) P.(ud_um) m_ad vpn wr Hview Had Hntr Hntf)
      as (w' & a & d & Hum' & Hwr).
    assert (Hw' : w' = w) by congruence. subst w'.
    (* ---- frame-cell address facts (2-slot frame: ra @ 1, s0 @ 2) ---- *)
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 2 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- +0x00 c.addi sp,-16 ---- *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int KernelSyms.uvmclear) (mword_of_int 48 : mword 6) mm K 2 b ltac:(lia) Hpush
              with "Hcg Hpc []").
    { iApply (ucli_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm) with W1.
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v8) "Hc1". iDestruct "S2" as (v0) "Hc2".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr)
      by (rewrite /W1 upd_eq; reflexivity).
    assert (Hpp02 : add_vec_int (mword_of_int KernelSyms.uvmclear : mword 64) 2 = mword_of_int (KernelSyms.uvmclear + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* ---- +0x02 c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmclear + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 2)%nat v8 b with "Hcg Hpc [] [Hc1]").
    { iApply (ucli_02 with "Htext"). }
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1".
    iEval (rewrite HspW1 Hb1; rgne) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r1) in "Hc1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.uvmclear + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.uvmclear + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- +0x04 c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmclear + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat v0 b with "Hcg Hpc [] [Hc2]").
    { iApply (ucli_04 with "Htext"). }
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2".
    iEval (rewrite HspW1 Hb2; rgne) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r8) in "Hc2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.uvmclear + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.uvmclear + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- +0x06 c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uvmclear + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ucli_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.uvmclear + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.uvmclear + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ---- +0x08 c.li a2,0 (walk's alloc argument) ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmclear + 0x08)) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) W2 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (ucli_08 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (W3 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> W2).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.uvmclear + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.uvmclear + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ---- +0x0a jal walk ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmclear + 0x0a)) (mword_of_int 1 : mword 5) (mword_of_int 2095796 : mword 21)
              W3 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (ucli_0a with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (W4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uvmclear + 0x0a) : mword 64) 4)]> W3).
    assert (Hpcwk : add_vec (mword_of_int (KernelSyms.uvmclear + 0x0a) : mword 64) (sign_extend' 64 (mword_of_int 2095796 : mword 21)) = mword_of_int KernelSyms.walk) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcwk) in "Hpc".
    (* ---- the register facts at walk's entry ---- *)
    assert (HW4sp : W4 !!! Regidx csp_rs1 = spr).
    { rewrite /W4 /W3 /W2.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact HspW1. }
    assert (HW4a0 : W4 !!! Regidx (mword_of_int 10 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hbase. exact Hroot. }
    assert (HW4a1 : W4 !!! Regidx (mword_of_int 11 : mword 5) = va).
    { rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      reflexivity. }
    assert (HW4a2 : W4 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int 0).
    { rewrite /W4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /W3 upd_eq. reflexivity. }
    assert (HW4ra : W4 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.uvmclear + 0x0a) : mword 64) 4)
      by (rewrite /W4 upd_eq; reflexivity).
    assert (Hret0e : ret_pc (W4 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.uvmclear + 0x0e)).
    { rewrite HW4ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    (* ---- the call ---- *)
    iApply (WalkNoalloc.wp_walk_noalloc_sconf KT1 W4 t m_ad (K - 2)%nat (DfracOwn 1) b p
              ltac:(lia) HW4a0 HW4a2
              ltac:(rewrite HW4a1; exact Hvab)
              Hrep
              with "Hcg Htext Hpc Hptree").
    iIntros (CID7 Hs7 mw) "Hcg Hpc Hptree %Hkcs %Hpay".
    iEval (rewrite Hret0e) in "Hpc".
    assert (HW4vpn : svpn_of (W4 !!! Regidx (mword_of_int 11 : mword 5)) = vpn)
      by (rewrite HW4a1; reflexivity).
    rewrite HW4vpn in Hpay.
    (* ---- the recovered register facts ---- *)
    assert (Hmwsp : mw !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HW4sp. }
    assert (Hmwagree : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> csp_rs1 ->
              mw !!! Regidx c = mm !!! Regidx c).
    { intros c Hc Hc8 Hcsp.
      rewrite (callee_saved_lookup Hkcs c Hc).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c;
           first [ apply Hc8; reflexivity | apply Hcsp; reflexivity | vm_compute in Hc; discriminate ] ]).
      reflexivity. }
    (* ================================================================= *)
    (* +0x0e c.beqz a0 : the panic arm is DEAD.                           *)
    (* ================================================================= *)
    destruct Hpay as [(Ha0z & Hnone) | (p2 & p1 & wv & Hl0 & Ha0v & Hverd)].
    { exfalso. rewrite Had in Hnone. discriminate. }
    assert (Hwv : wv = wr).
    { destruct Hverd as [Hs | (_ & Hn)].
      - rewrite Had in Hs. injection Hs as Hs. exact (eq_sym Hs).
      - rewrite Had in Hn. discriminate. }
    subst wv.
    (* lend the level-0 slot out of the tree *)
    iDestruct (ptree_own_level0_upd (DfracOwn 1) t vpn p2 p1 wr Hl0 with "Hptree")
      as "(#Hcl0 & Hcell & Hclose)".
    iDestruct (ucl_claim_pv with "Hcl0") as %Hpv0.
    assert (Ha0nz : eq_vec (mw !!! Regidx (mword_of_int 10 : mword 5)) zero_reg = false).
    { rewrite Ha0v. unfold pt_addr0. exact (ucl_slot_nonzero _ _ Hpv0). }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.uvmclear + 0x0e)) (mword_of_int 8 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              mw (K - 2)%nat b
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              Ha0nz
              with "Hcg Hpc []").
    { iApply (ucli_0e with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.uvmclear + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.uvmclear + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* ---- +0x10 c.ld a5,0(a0) : a5 = *pte ---- *)
    assert (Hea0 : forall X : mword 64,
        add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iDestruct (pt_slot_phys_to_mem (u_next_base p1) (vpn_idx 0 vpn) (DfracOwn 1) wr
                 with "Hcl0 Hcell") as "Hcell".
    iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.uvmclear + 0x10)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12)
              mw (K - 2)%nat wr b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hcell]").
    { iApply (ucli_10 with "Htext"). }
    { iEval (rewrite Hea0; rgne; rewrite Ha0v). iExact "Hcell". }
    iIntros (CID9 Hs9) "Hcg Hpc Hcell".
    iEval (rewrite Hea0; rgne; rewrite Ha0v) in "Hcell".
    set (B1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg wr]> mw).
    assert (HB1a5 : B1 !!! Regidx (mword_of_int 15 : mword 5) = wr)
      by (rewrite /B1 upd_eq; reflexivity).
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.uvmclear + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.uvmclear + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ---- +0x12 c.andi a5,a5,-17 : a5 &= ~PTE_U ---- *)
    iApply (wp_candi_s_sconf (mword_of_int (KernelSyms.uvmclear + 0x12)) (mword_of_int 15 : mword 5) (mword_of_int 47 : mword 6)
              B1 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ucli_12 with "Htext"). }
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (B2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (rget B1 (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 47 : mword 6))))]> B1).
    assert (HB2a5 : B2 !!! Regidx (mword_of_int 15 : mword 5) = pte_clear_u wr).
    { rewrite /B2 upd_eq. rgne. rewrite HB1a5. exact (pte_clear_u_andi12 wr). }
    assert (HB2a0 : B2 !!! Regidx (mword_of_int 10 : mword 5) = pt_addr0 p1 vpn).
    { rewrite /B2. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite upd_ne; [| vm_compute; discriminate].
      exact Ha0v. }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.uvmclear + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.uvmclear + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* ---- +0x14 c.sd a5,0(a0) : *pte = a5 ---- *)
    iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.uvmclear + 0x14)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12) B2 (K - 2)%nat wr b
              with "Hcg Hpc [] [Hcell]").
    { iApply (ucli_14 with "Htext"). }
    { iEval (rewrite Hea0; rgne; rewrite HB2a0). iExact "Hcell". }
    iIntros (CID11 Hs11) "Hcg Hpc Hcell".
    iEval (rewrite Hea0; rgne; rewrite HB2a0; rgne; rewrite HB2a5) in "Hcell".
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.uvmclear + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.uvmclear + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* ================================================================= *)
    (* CLOSE the invariant at [uptd_set P vpn (pte_clear_u w)].            *)
    (* ================================================================= *)
    iDestruct (pt_slot_mem_to_phys (u_next_base p1) (vpn_idx 0 vpn) (DfracOwn 1) (pte_clear_u wr)
                 with "Hcl0 Hcell") as "Hcell".
    iDestruct ("Hclose" $! (pte_clear_u wr) with "Hcell") as "Hptree".
    assert (Hclr : pte_clear_u wr = pte_set_ad (pte_clear_u w) a d).
    { rewrite Hwr. exact (pte_set_ad_clear_u w a d). }
    iEval (rewrite Hclr) in "Hptree".
    assert (Hwf' : proc_pt_wf (uptd_set P vpn (pte_clear_u w)))
      by exact (proc_pt_wf_clear_u P vpn w Hwf Hum Hperm).
    assert (HPnum : (uptd_set P vpn (pte_clear_u w)).(ud_um)
                    = <[vpn := pte_clear_u w]> P.(ud_um)) by reflexivity.
    assert (HPntfp : (uptd_set P vpn (pte_clear_u w)).(ud_tfp) = P.(ud_tfp)) by reflexivity.
    assert (HPnroot : (uptd_set P vpn (pte_clear_u w)).(ud_root) = P.(ud_root)) by reflexivity.
    assert (HPnl : (uptd_set P vpn (pte_clear_u w)).(ud_um) !! vpn = Some (pte_clear_u w))
      by (rewrite HPnum; apply lookup_insert).
    destruct (proj1 Hwf' vpn (pte_clear_u w) HPnl) as (_ & Hleafs).
    destruct (Hleafs a d) as (Hlv & Hll & Hln & Hlp).
    assert (Hrep' : pt_rep0 (ptree_set_leaf t vpn (pte_set_ad (pte_clear_u w) a d))
                            (<[vpn := pte_set_ad (pte_clear_u w) a d]> m_ad))
      by exact (pt_rep0_insert t m_ad vpn p2 p1 wr (pte_set_ad (pte_clear_u w) a d)
                  Hrep Hl0 Hlv Hll Hln Hlp).
    assert (Hview' : upt_ad_view (uptd_set P vpn (pte_clear_u w)).(ud_tfp)
                                 (uptd_set P vpn (pte_clear_u w)).(ud_um)
                                 (<[vpn := pte_set_ad (pte_clear_u w) a d]> m_ad)).
    { rewrite HPntfp HPnum.
      exact (upt_ad_view_set P.(ud_tfp) P.(ud_um) m_ad vpn w (pte_clear_u w) a d
               Hmapwf Hview Hum). }
    assert (Hbase' : pt_base (ptree_set_leaf t vpn (pte_set_ad (pte_clear_u w) a d))
                     = (uptd_set P vpn (pte_clear_u w)).(ud_root)).
    { rewrite ptree_set_leaf_base HPnroot. exact Hbase. }
    iDestruct ((proc_pt_own_set_same P vpn w (pte_clear_u w) Hum (pte_ppn_clear_u w))
                 with "Hown") as "Hown".
    iDestruct (proc_pt_rebuild (uptd_set P vpn (pte_clear_u w))
                 (ptree_set_leaf t vpn (pte_set_ad (pte_clear_u w) a d))
                 (<[vpn := pte_set_ad (pte_clear_u w) a d]> m_ad)
                 Hwf' Hview' Hrep' Hbase' with "Hptree Hown") as "Hpt".
    (* ================================================================= *)
    (* +0x16..+0x1c: the epilogue.                                        *)
    (* ================================================================= *)
    assert (HspB2 : B2 !!! Regidx csp_rs1 = spr).
    { rewrite /B2. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite upd_ne; [| vm_compute; discriminate].
      exact Hmwsp. }
    assert (HB2agree : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> csp_rs1 ->
              B2 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc Hc8 Hcsp.
      rewrite /B2. rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hc; discriminate].
      rewrite /B1. rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hc; discriminate].
      apply Hmwagree; assumption. }
    (* +0x16 c.ldsp ra,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmclear + 0x16)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              B2 (K - 2)%nat (mm !!! Regidx (mword_of_int 1)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc1]").
    { iApply (ucli_16 with "Htext"). }
    { iEval (rewrite HspB2 Hb1). iExact "Hc1". }
    iIntros (CID12 Hs12) "Hcg Hpc Hc1".
    iEval (rewrite HspB2 Hb1) in "Hc1".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1))]> B2).
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.uvmclear + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.uvmclear + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.ldsp s0,0(sp) *)
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
    { rewrite /E1. rewrite upd_ne; [| vm_compute; discriminate]. exact HspB2. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmclear + 0x18)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 2)%nat (mm !!! Regidx (mword_of_int 8)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc2]").
    { iApply (ucli_18 with "Htext"). }
    { iEval (rewrite HspE1 Hb2). iExact "Hc2". }
    iIntros (CID13 Hs13) "Hcg Hpc Hc2".
    iEval (rewrite HspE1 Hb2) in "Hc2".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8))]> E1).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.uvmclear + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.uvmclear + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.addi sp,+16 : the frame pop *)
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spr).
    { rewrite /E2. rewrite upd_ne; [| vm_compute; discriminate]. exact HspE1. }
    set (E3 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    assert (HspE3 : E3 !!! Regidx csp_rs1 = sp0).
    { rewrite /E3 upd_eq. rewrite HspE2.
      unfold regval_into_reg, spr, sp0. apply frame_cancel_16. }
    assert (Hwvsp : add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite -HspE3. rewrite /E3 upd_eq. reflexivity. }
    assert (Hpop : E2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwvsp HspE2. symmetry. exact Hsprstk. }
    iAssert (stack_own (KTR := KT1) sp0 2) with "[Hc1 Hc2]" as "Hfr".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
      iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
      done. }
    iEval (rewrite -Hwvsp) in "Hfr".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.uvmclear + 0x1a)) (mword_of_int 16 : mword 6)
              E2 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc [] Hfr").
    { iApply (ucli_1a with "Htext"). }
    iIntros (CID14 Hs14) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2) with E3.
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.uvmclear + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.uvmclear + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.ret *)
    assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /E3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /E2. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq. reflexivity. }
    assert (HE3peel : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> csp_rs1 ->
              E3 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc Hc8 Hcsp.
      rewrite /E3. rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c; apply Hcsp; reflexivity].
      rewrite /E2. rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c; apply Hc8; reflexivity].
      rewrite /E1. rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hc; discriminate].
      apply HB2agree; assumption. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uvmclear + 0x1c)) (mword_of_int 1 : mword 5) E3 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc []").
    { iApply (ucli_1c with "Htext"). }
    iIntros (CID15 Hs15) "Hcg Hpc".
    iEval (rgne; rewrite HE3ra) in "Hpc".
    iSpecialize ("Hcont" $! CID15 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E3 with "Hcg Hpc [%] Hpt").
    (* callee_saved mm E3 *)
    unfold callee_saved. split_and!.
    - rewrite HspE3. reflexivity.
    - rewrite /E3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_eq. reflexivity.
    - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
    - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
    - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
    - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
    - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
    - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
    - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
    - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
    - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
    - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
    - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
  Qed.

End ProofUvmclear.

End UvmclearProof.
