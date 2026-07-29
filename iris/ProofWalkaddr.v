(* ProofWalkaddr.v -- walkaddr() over the SIE-agnostic sconf world.

     uint64 walkaddr(pagetable_t pagetable, uint64 va) {
       if (va >= MAXVA) return 0;
       pte_t *pte = walk(pagetable, va, 0);
       if (pte == 0) return 0;
       if (( *pte & (PTE_V|PTE_U)) != (PTE_V|PTE_U)) return 0;
       return PTE2PA( *pte);
     }

   A 2-slot-frame wrapper around the NO-ALLOC walk (SpecWalk's
   [WALK_NOALLOC]), in the shape of ProofIsmapped.v: one call, one join at
   the epilogue.  Two things distinguish it:

   - the [va >= MAXVA] test at +0x04 splits BEFORE the frame is pushed, so
     that arm returns at +0x0a with no stack traffic and the tree untouched;
     only the three later exits share the 2-slot epilogue at +0x2a, through
     one [iAssert]ed continuation (the pipeclose join recipe -- [ptree_own]
     is a wand ARGUMENT of the join, not captured, because the slot-reading
     arm consumes and restores it);
   - the two C flag tests are merged into [andi a3,a5,17] / [li a4,17] /
     [beq], and the return value is [PTE2PA] = [srli 10; slli 12].

   ===================================================================
   The pure content this proof needs -- the [andi ...,17] V&U bit test
   ([PtBuild.pte_vu_bits]), the [srli 10; slli 12] PTE2PA identity
   ([ProcPtOwn.pte2pa]) and the [uint w < 2^54] bound a model-valid leaf
   carries ([PtTree.pte_hi_zero]) -- all lives at its own altitude now; only
   the MAXVA literal below is walkaddr's own.  *)
From Stdlib Require Import Eqdep_dec ZArith Lia List Bool.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import CommonWalk PtTree.
Require Import KptTree.   (* pt_slot_phys_to_mem / pt_slot_mem_to_phys *)
Require Import PtBuild.
Require Import ProcPtOwn.
Require Import WpWalkaddrDecode.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecWalk.
Require Import SpecWalkaddr.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.


(* ===================================================================== *)
(* THE ONE PURE FACT THAT IS WALKADDR'S OWN: the MAXVA test.              *)
(*   [li a5,-1; srli a5,26] materializes 2^38-1, and the [bgeu a5,a1] that *)
(*   follows takes the fall-through arm exactly when [va < MAXVA].         *)
(* ===================================================================== *)
Lemma wa_z_maxva (x : Z) : Z.geb 274877906943 x = true -> x < 2 ^ 38.
Proof.
  intros H. apply Z.geb_le in H.
  assert (P : 2 ^ 38 = 274877906944) by (vm_compute; reflexivity).
  rewrite P. lia.
Qed.


(* ===================================================================== *)
(* THE WHOLE FUNCTION.                                                    *)
(* ===================================================================== *)

Module WalkaddrProof (WalkNoalloc : WALK_NOALLOC) : WALKADDR.

Section ProofWalkaddr.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_walkaddr_sconf
      (γ : gname) (Φ : mval -> iProp Σ) (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (K : nat) (dq : dfrac)
    : wp_walkaddr_sconf_body γ Φ mm t m K dq.
  Proof.
    cbv beta delta [wp_walkaddr_sconf_body].
    intros pcE va vpn ret_tgt HK Hroot Hrep.
    iIntros "Hcg #Htext Hpc Hptree Hcont".
    iPoseProof (wai_00 with "Htext") as "Hi00".
    iPoseProof (wai_02 with "Htext") as "Hi02".
    iPoseProof (wai_04 with "Htext") as "Hi04".
    (* ---- +0x00 c.li a5,-1 ---- *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int WA) (mword_of_int 15 : mword 5)
              (mword_of_int 63 : mword 6) (mword_of_int 18446744073709551615 : mword 64) mm K
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hpc".
    set (V1 := <[Regidx (mword_of_int 15 : mword 5) :=
        regval_into_reg (mword_of_int 18446744073709551615 : mword 64)]> mm).
    assert (Hpp02 : add_vec_int (mword_of_int WA : mword 64) 2 = mword_of_int (WA + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* ---- +0x02 c.srli a5,a5,0x1a : a5 := 2^38 - 1 ---- *)
    iApply (wp_csrli_s_sconf γ Φ (mword_of_int (WA + 0x02)) (Cregidx (mword_of_int 7))
              (mword_of_int 15 : mword 5) (mword_of_int 26 : mword 6) V1 K
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi02 [-]").
    iIntros "Hcg Hpc".
    set (V2 := <[Regidx (mword_of_int 15 : mword 5) :=
        regval_into_reg (mword_of_int 274877906943 : mword 64)]> mm).
    assert (HV2c : <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (V1 !!! Regidx (mword_of_int 15 : mword 5))
           (subrange_vec_dec (mword_of_int 26 : mword 6) (Z.sub log2_xlen 1) 0))]> V1 = V2).
    { rewrite /V2 /V1 upd_upd. do 2 f_equal. rewrite upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite HV2c) in "Hcg".
    assert (Hpp04 : add_vec_int (mword_of_int (WA + 0x02) : mword 64) 2 = mword_of_int (WA + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    assert (HV2a5 : V2 !!! Regidx (mword_of_int 15 : mword 5)
                    = (mword_of_int 274877906943 : mword 64))
      by (rewrite /V2 upd_eq; reflexivity).
    assert (HV2a1 : V2 !!! Regidx (mword_of_int 11 : mword 5) = va)
      by (rewrite /V2; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hcmp : zopz0zKzJ_u (V2 !!! Regidx (mword_of_int 15 : mword 5))
                     (V2 !!! Regidx (mword_of_int 11 : mword 5))
                   = Z.geb 274877906943 (uint va)).
    { unfold zopz0zKzJ_u. rewrite HV2a5. rewrite HV2a1.
      assert (Hu : uint (mword_of_int 274877906943 : mword 64) = 274877906943)
        by (vm_compute; reflexivity).
      rewrite Hu. reflexivity. }
    (* ================================================================= *)
    (* +0x04 bgeu a5,a1 : the MAXVA test.  The FALL-THROUGH arm returns 0 *)
    (* at +0x0a without ever pushing a frame.                             *)
    (* ================================================================= *)
    destruct (Z.geb 274877906943 (uint va)) eqn:Hge.
    2:{ iPoseProof (wai_08 with "Htext") as "Hi08".
        iPoseProof (wai_0a with "Htext") as "Hi0a".
        iApply (wp_bgeu_fall_s_sconf γ Φ (mword_of_int (WA + 0x04)) (mword_of_int 8 : mword 13)
                  (mword_of_int 11 : mword 5) (mword_of_int 15 : mword 5) V2 K
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(exact Hcmp)
                  with "Hcg Hpc Hi04 [-]").
        iIntros "Hcg Hpc".
        assert (Hpp08 : add_vec_int (mword_of_int (WA + 0x04) : mword 64) 4
                        = mword_of_int (WA + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp08) in "Hpc".
        (* +0x08 c.li a0,0 *)
        iApply (wp_cli_s_sconf γ Φ (mword_of_int (WA + 0x08)) (mword_of_int 10 : mword 5)
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) V2 K
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi08 [-]").
        iIntros "Hcg Hpc".
        set (V3 := <[Regidx (mword_of_int 10 : mword 5) :=
            regval_into_reg (mword_of_int 0 : mword 64)]> V2).
        assert (Hpp0a : add_vec_int (mword_of_int (WA + 0x08) : mword 64) 2
                        = mword_of_int (WA + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp0a) in "Hpc".
        assert (HV3ra : V3 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
        { rewrite /V3. rewrite upd_ne; [| vm_compute; discriminate].
          rewrite /V2. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
        assert (Hrt : ret_pc (V3 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
          by (rewrite HV3ra; reflexivity).
        (* +0x0a c.ret *)
        iApply (wp_cret_s_sconf γ Φ (mword_of_int (WA + 0x0a)) (mword_of_int 1 : mword 5) V3 K
                  ltac:(vm_compute; discriminate) with "Hcg Hpc Hi0a [-]").
        iIntros "Hcg Hpc".
        iEval (rewrite Hrt) in "Hpc".
        iApply ("Hcont" $! V3 with "Hcg Hpc Hptree [%] [%]").
        { rewrite /V3. apply callee_saved_insert_r; [vm_compute; reflexivity |].
          rewrite /V2. apply callee_saved_insert_r; [vm_compute; reflexivity |].
          apply callee_saved_refl. }
        { left. rewrite /V3 upd_eq. reflexivity. } }
    (* ---- va < MAXVA: the branch is TAKEN, into the framed body ------- *)
    assert (Hvalt : (uint va < 2 ^ 38)%Z) by (apply wa_z_maxva; exact Hge).
    iApply (wp_bgeu_taken_s_sconf γ Φ (mword_of_int (WA + 0x04)) (mword_of_int 8 : mword 13)
              (mword_of_int 11 : mword 5) (mword_of_int 15 : mword 5) V2 K
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(exact Hcmp) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi04 [-]").
    iNext. iIntros "Hcg Hpc".
    assert (Htgt0c : add_vec (mword_of_int (WA + 0x04) : mword 64)
              (sign_extend' 64 (mword_of_int 8 : mword 13)) = mword_of_int (WA + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt0c) in "Hpc".
    (* ================================================================= *)
    (* The 2-slot frame.                                                  *)
    (* ================================================================= *)
    pose (sp0 := (V2 !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (V2 !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> V2).
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 2 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpush : add_vec (V2 !!! Regidx csp_rs1)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
            = pa_stk (V2 !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (wai_0c with "Htext") as "Hi0c".
    iPoseProof (wai_0e with "Htext") as "Hi0e".
    iPoseProof (wai_10 with "Htext") as "Hi10".
    iPoseProof (wai_12 with "Htext") as "Hi12".
    iPoseProof (wai_14 with "Htext") as "Hi14".
    iPoseProof (wai_16 with "Htext") as "Hi16".
    (* +0x0c c.addi sp,-16 *)
    iApply (wp_caddi_sp_push_s_sconf γ Φ (mword_of_int (WA + 0x0c)) (mword_of_int 48 : mword 6)
              V2 K 2 ltac:(lia) Hpush with "Hcg Hpc Hi0c [-]").
    iIntros "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (V2 !!! Regidx csp_rs1)
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> V2) with W1.
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v8) "Hc1". iDestruct "S2" as (v0) "Hc2".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr) by (rewrite /W1 upd_eq; reflexivity).
    assert (Hpp0e : add_vec_int (mword_of_int (WA + 0x0c) : mword 64) 2
                    = mword_of_int (WA + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (WA + 0x0e)) (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 5) W1 (K - 2)%nat v8 with "Hcg Hpc Hi0e [Hc1] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros "Hcg Hpc Hc1".
    iEval (rewrite HspW1 Hb1) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /W1. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /V2. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r1) in "Hc1".
    assert (Hpp10 : add_vec_int (mword_of_int (WA + 0x0e) : mword 64) 2
                    = mword_of_int (WA + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (WA + 0x10)) (mword_of_int 0 : mword 6)
              (mword_of_int 8 : mword 5) W1 (K - 2)%nat v0 with "Hcg Hpc Hi10 [Hc2] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros "Hcg Hpc Hc2".
    iEval (rewrite HspW1 Hb2) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
    { rewrite /W1. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /V2. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r8) in "Hc2".
    assert (Hpp12 : add_vec_int (mword_of_int (WA + 0x10) : mword 64) 2
                    = mword_of_int (WA + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (WA + 0x12)) (Cregidx (mword_of_int 0))
              (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5) W1 (K - 2)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi12 [-]").
    iIntros "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hpp14 : add_vec_int (mword_of_int (WA + 0x12) : mword 64) 2
                    = mword_of_int (WA + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.li a2,0 (walk's alloc argument) *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (WA + 0x14)) (mword_of_int 12 : mword 5)
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) W2 (K - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi14 [-]").
    iIntros "Hcg Hpc".
    set (W3 := <[Regidx (mword_of_int 12 : mword 5) :=
        regval_into_reg (mword_of_int 0 : mword 64)]> W2).
    assert (Hpp16 : add_vec_int (mword_of_int (WA + 0x14) : mword 64) 2
                    = mword_of_int (WA + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 jal ra,walk *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (WA + 0x16)) (mword_of_int 1 : mword 5)
              (mword_of_int 2096976 : mword 21) W3 (K - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi16 [-]").
    iIntros "Hcg Hpc".
    set (W4 := <[Regidx (mword_of_int 1 : mword 5) :=
        regval_into_reg (add_vec_int (mword_of_int (WA + 0x16) : mword 64) 4)]> W3).
    assert (Hpcwk : add_vec (mword_of_int (WA + 0x16) : mword 64)
              (sign_extend' 64 (mword_of_int 2096976 : mword 21))
            = mword_of_int KernelSyms.walk) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcwk) in "Hpc".
    (* ---- the register facts at walk's entry ---- *)
    assert (HW4sp : W4 !!! Regidx csp_rs1 = spr).
    { rewrite /W4 /W3 /W2.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact HspW1. }
    assert (HW4a0 : W4 !!! Regidx (mword_of_int 10 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite /W4 /W3 /W2 /W1 /V2.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact Hroot. }
    assert (HW4a1 : W4 !!! Regidx (mword_of_int 11 : mword 5) = va).
    { rewrite /W4 /W3 /W2 /W1 /V2.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      reflexivity. }
    assert (HW4a2 : W4 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int 0).
    { rewrite /W4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /W3 upd_eq. reflexivity. }
    assert (HW4ra : W4 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (WA + 0x16) : mword 64) 4)
      by (rewrite /W4 upd_eq; reflexivity).
    assert (Hret1a : ret_pc (W4 !!! Regidx (mword_of_int 1 : mword 5))
                     = mword_of_int (WA + 0x1a)).
    { rewrite HW4ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    assert (Hwkva : (uint (W4 !!! Regidx (mword_of_int 11 : mword 5)) < 2 ^ 38)%Z)
      by (rewrite HW4a1; exact Hvalt).
    assert (HKw : (8 <= K - 2)%nat) by lia.
    (* ---- the call ---- *)
    iApply (WalkNoalloc.wp_walk_noalloc_sconf γ Φ W4 t m (K - 2)%nat dq
              HKw HW4a0 HW4a2 Hwkva Hrep
              with "Hcg Htext Hpc Hptree [-]").
    iIntros (mw) "Hcg Hpc Hptree %Hkcs %Hpay".
    iEval (rewrite Hret1a) in "Hpc".
    assert (HW4vpn : svpn_of (W4 !!! Regidx (mword_of_int 11 : mword 5)) = vpn)
      by (rewrite HW4a1; reflexivity).
    rewrite HW4vpn in Hpay.
    assert (Hmwsp : mw !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HW4sp. }
    assert (Hmwagree : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> csp_rs1 ->
              mw !!! Regidx c = mm !!! Regidx c).
    { intros c Hc Hc8 Hcsp.
      rewrite (callee_saved_lookup Hkcs c Hc).
      rewrite /W4 /W3 /W2 /W1 /V2.
      repeat (rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c;
           first [ apply Hc8; reflexivity | apply Hcsp; reflexivity
                 | vm_compute in Hc; discriminate ] ]).
      reflexivity. }
    (* ================================================================= *)
    (* THE JOIN at +0x2a: pop the frame and return, whatever a0 holds.    *)
    (* ================================================================= *)
    iAssert (∀ (M : regfile),
               ⌜callee_saved mw M⌝ -∗
               sie_cap_gpr γ M (K - 2)%nat -∗
               pc_is (mword_of_int (WA + 0x2a) : mword 64) -∗
               ptree_own 2 dq t -∗
               ⌜ M !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0
                 \/ (exists w, m !! vpn = Some w /\ pte_vu w /\
                       M !!! Regidx (mword_of_int 10 : mword 5) = page_base (pte_ppn w)) ⌝ -∗
               WP (Loop : expr riscv_lang) {{ Φ }})%I
      with "[Hcont Hc1 Hc2]" as "EPI".
    { iIntros (M) "%HcsM Hcg Hpc Hptree %Hpay'".
      assert (HspM : M !!! Regidx csp_rs1 = spr).
      { rewrite (callee_saved_lookup HcsM csp_rs1 ltac:(vm_compute; reflexivity)).
        exact Hmwsp. }
      assert (HMagree : forall c : mword 5, is_cs_idx c = true ->
                c <> mword_of_int 8 -> c <> csp_rs1 ->
                M !!! Regidx c = mm !!! Regidx c).
      { intros c Hc Hc8 Hcsp.
        rewrite (callee_saved_lookup HcsM c Hc). apply Hmwagree; assumption. }
      iPoseProof (wai_2a with "Htext") as "Hi2a".
      iPoseProof (wai_2c with "Htext") as "Hi2c".
      iPoseProof (wai_2e with "Htext") as "Hi2e".
      iPoseProof (wai_30 with "Htext") as "Hi30".
      (* +0x2a c.ldsp ra,8(sp) *)
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (WA + 0x2a)) (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 5) M (K - 2)%nat (mm !!! Regidx (mword_of_int 1))
                (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi2a [Hc1] [-]").
      { iEval (rewrite HspM Hb1). iExact "Hc1". }
      iIntros "Hcg Hpc Hc1".
      iEval (rewrite HspM Hb1) in "Hc1".
      set (E1 := <[Regidx (mword_of_int 1 : mword 5) :=
          regval_into_reg (mm !!! Regidx (mword_of_int 1))]> M).
      assert (Hpp2c : add_vec_int (mword_of_int (WA + 0x2a) : mword 64) 2
                      = mword_of_int (WA + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2c) in "Hpc".
      (* +0x2c c.ldsp s0,0(sp) *)
      assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
      { rewrite /E1. rewrite upd_ne; [| vm_compute; discriminate]. exact HspM. }
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (WA + 0x2c)) (mword_of_int 0 : mword 6)
                (mword_of_int 8 : mword 5) E1 (K - 2)%nat (mm !!! Regidx (mword_of_int 8))
                (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi2c [Hc2] [-]").
      { iEval (rewrite HspE1 Hb2). iExact "Hc2". }
      iIntros "Hcg Hpc Hc2".
      iEval (rewrite HspE1 Hb2) in "Hc2".
      set (E2 := <[Regidx (mword_of_int 8 : mword 5) :=
          regval_into_reg (mm !!! Regidx (mword_of_int 8))]> E1).
      assert (Hpp2e : add_vec_int (mword_of_int (WA + 0x2c) : mword 64) 2
                      = mword_of_int (WA + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      (* +0x2e c.addi sp,+16 : the frame pop *)
      assert (HspE2 : E2 !!! Regidx csp_rs1 = spr).
      { rewrite /E2. rewrite upd_ne; [| vm_compute; discriminate]. exact HspE1. }
      set (E3 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (E2 !!! Regidx csp_rs1)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
      assert (HspE3 : E3 !!! Regidx csp_rs1 = sp0).
      { rewrite /E3 upd_eq. rewrite HspE2.
        unfold regval_into_reg, spr, sp0. apply frame_cancel_16. }
      assert (Hwv : add_vec (E2 !!! Regidx csp_rs1)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
      { rewrite -HspE3. rewrite /E3 upd_eq. reflexivity. }
      assert (Hpop : E2 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E2 !!! Regidx csp_rs1)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
      { rewrite Hwv HspE2. symmetry. exact Hsprstk. }
      iAssert (stack_own sp0 2) with "[Hc1 Hc2]" as "Hfr".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
        iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
        done. }
      iEval (rewrite -Hwv) in "Hfr".
      iApply (wp_caddi_sp_pop_s_sconf γ Φ (mword_of_int (WA + 0x2e)) (mword_of_int 16 : mword 6)
                E2 (K - 2)%nat 2 Hpop with "Hcg Hpc Hi2e Hfr [-]").
      iIntros "Hcg Hpc".
      change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1)
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2) with E3.
      assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      assert (Hpp30 : add_vec_int (mword_of_int (WA + 0x2e) : mword 64) 2
                      = mword_of_int (WA + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp30) in "Hpc".
      (* +0x30 c.ret *)
      assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
      { rewrite /E3. rewrite upd_ne; [| vm_compute; discriminate].
        rewrite /E2. rewrite upd_ne; [| vm_compute; discriminate].
        rewrite /E1 upd_eq. reflexivity. }
      assert (HE3a0 : E3 !!! Regidx (mword_of_int 10 : mword 5)
                      = M !!! Regidx (mword_of_int 10 : mword 5)).
      { rewrite /E3. rewrite upd_ne; [| vm_compute; discriminate].
        rewrite /E2. rewrite upd_ne; [| vm_compute; discriminate].
        rewrite /E1. rewrite upd_ne; [| vm_compute; discriminate]. reflexivity. }
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
        apply HMagree; assumption. }
      assert (Hrt : ret_pc (E3 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
        by (rewrite HE3ra; reflexivity).
      iApply (wp_cret_s_sconf γ Φ (mword_of_int (WA + 0x30)) (mword_of_int 1 : mword 5) E3 K
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hi30 [-]").
      iIntros "Hcg Hpc".
      iEval (rewrite Hrt) in "Hpc".
      iApply ("Hcont" $! E3 with "Hcg Hpc Hptree [%] [%]").
      { unfold callee_saved. split_and!.
        - rewrite HspE3. rewrite /sp0 /V2.
          rewrite upd_ne; [reflexivity | vm_compute; discriminate].
        - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
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
        - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. }
      { rewrite HE3a0. destruct Hpay' as [Hz | (w & Hsome & Hvu & Ha0)].
        - left. exact Hz.
        - right. exists w. split; [exact Hsome |]. split; [exact Hvu |].
          split; [exact Hvalt | exact Ha0]. } }
    (* ================================================================= *)
    (* +0x1a c.beqz a0 : the walk verdict.                                *)
    (* ================================================================= *)
    iPoseProof (wai_1a with "Htext") as "Hi1a".
    destruct Hpay as [(Ha0z & Hnone) | (p2 & p1 & w0 & Hl0 & Ha0v & Hverd)].
    { (* ---- walk returned NULL: branch TAKEN, a0 = 0 already ---- *)
      iApply (wp_cbeqz_taken_s_sconf γ Φ (mword_of_int (WA + 0x1a)) (mword_of_int 8 : mword 8)
                (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5) mw (K - 2)%nat
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0z; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1a [-]").
      iNext. iIntros "Hcg Hpc".
      assert (Htgt2a : add_vec (mword_of_int (WA + 0x1a) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 8 : mword 8) ('b"0"))))
              = mword_of_int (WA + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt2a) in "Hpc".
      iApply ("EPI" $! mw with "[%] Hcg Hpc Hptree [%]").
      { apply callee_saved_refl. }
      { left. exact Ha0z. } }
    (* ---- walk returned the L0 slot address: read it ---- *)
    iDestruct (ptree_own_level0_ro dq t vpn p2 p1 w0 Hl0 with "Hptree") as "(#Hcl0 & Hcell & Hclose)".
    iDestruct (phys_word_pointsto_ram with "Hcell") as %Hslotram.
    iDestruct (pt_slot_phys_to_mem (u_next_base p1) (vpn_idx 0 vpn) dq w0
                 with "Hcl0 Hcell") as "Hcell".
    assert (Ha0nz : mw !!! Regidx (mword_of_int 10 : mword 5) <> mword_of_int 0).
    { rewrite Ha0v. intro Heq. rewrite Heq in Hslotram.
      unfold addr_is_ram in Hslotram. destruct Hslotram as [Hlo _].
      apply (proj2 (Z.leb_le _ _)) in Hlo. vm_compute in Hlo. discriminate. }
    iPoseProof (wai_1c with "Htext") as "Hi1c".
    iPoseProof (wai_1e with "Htext") as "Hi1e".
    iPoseProof (wai_22 with "Htext") as "Hi22".
    iPoseProof (wai_24 with "Htext") as "Hi24".
    iPoseProof (wai_26 with "Htext") as "Hi26".
    (* +0x1a c.beqz a0 FALLS *)
    iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (WA + 0x1a)) (mword_of_int 8 : mword 8)
              (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5) mw (K - 2)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(apply eq_vec_false_iff; intro He; apply Ha0nz;
                    rewrite He; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi1a [-]").
    iIntros "Hcg Hpc".
    assert (Hpp1c : add_vec_int (mword_of_int (WA + 0x1a) : mword 64) 2
                    = mword_of_int (WA + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.ld a5,0(a0) *)
    assert (Hea0 : forall X : mword 64,
        add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (WA + 0x1c)) (mword_of_int 15 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 0 : mword 12)
              mw (K - 2)%nat w0 (dqm:=dq)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1c [Hcell] [-]").
    { iEval (rewrite Hea0 Ha0v). iExact "Hcell". }
    iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hea0 Ha0v) in "Hcell".
    set (B1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w0]> mw).
    assert (HB1a5 : B1 !!! Regidx (mword_of_int 15 : mword 5) = w0)
      by (rewrite /B1 upd_eq; reflexivity).
    assert (Hpp1e : add_vec_int (mword_of_int (WA + 0x1c) : mword 64) 2
                    = mword_of_int (WA + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* give the tree back: the slot is untouched *)
    iDestruct (pt_slot_mem_to_phys (u_next_base p1) (vpn_idx 0 vpn) dq w0
                 with "Hcl0 Hcell") as "Hcell".
    iDestruct ("Hclose" with "Hcell") as "Hptree".
    (* +0x1e andi a3,a5,17 *)
    iApply (wp_andi_s_sconf γ Φ (mword_of_int (WA + 0x1e)) (mword_of_int 13 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 17 : mword 12)
              (and_vec w0 (sign_extend' 64 (mword_of_int 17 : mword 12))) B1 (K - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HB1a5; reflexivity)
              with "Hcg Hpc Hi1e [-]").
    iIntros "Hcg Hpc".
    set (B2 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg
        (and_vec w0 (sign_extend' 64 (mword_of_int 17 : mword 12)))]> B1).
    assert (Hpp22 : add_vec_int (mword_of_int (WA + 0x1e) : mword 64) 4
                    = mword_of_int (WA + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 c.li a4,17 *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (WA + 0x22)) (mword_of_int 14 : mword 5)
              (mword_of_int 17 : mword 6) (mword_of_int 17 : mword 64) B2 (K - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi22 [-]").
    iIntros "Hcg Hpc".
    set (B3 := <[Regidx (mword_of_int 14 : mword 5) :=
        regval_into_reg (mword_of_int 17 : mword 64)]> B2).
    assert (Hpp24 : add_vec_int (mword_of_int (WA + 0x22) : mword 64) 2
                    = mword_of_int (WA + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* +0x24 c.li a0,0 : the 0 return, set before the test *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (WA + 0x24)) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) B3 (K - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi24 [-]").
    iIntros "Hcg Hpc".
    set (B4 := <[Regidx (mword_of_int 10 : mword 5) :=
        regval_into_reg (mword_of_int 0 : mword 64)]> B3).
    assert (Hpp26 : add_vec_int (mword_of_int (WA + 0x24) : mword 64) 2
                    = mword_of_int (WA + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    assert (HB4a3 : B4 !!! Regidx (mword_of_int 13 : mword 5)
                    = and_vec w0 (sign_extend' 64 (mword_of_int 17 : mword 12))).
    { rewrite /B4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /B3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /B2 upd_eq. reflexivity. }
    assert (HB4a4 : B4 !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int 17 : mword 64)).
    { rewrite /B4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_eq. reflexivity. }
    assert (HB4a0 : B4 !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64))
      by (rewrite /B4 upd_eq; reflexivity).
    assert (HB4a5 : B4 !!! Regidx (mword_of_int 15 : mword 5) = w0).
    { rewrite /B4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /B3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /B2. rewrite upd_ne; [| vm_compute; discriminate].
      exact HB1a5. }
    assert (HcsB4 : callee_saved mw B4).
    { rewrite /B4. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /B3. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /B2. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /B1. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      apply callee_saved_refl. }
    (* ---- the slot's two sub-verdicts ---- *)
    destruct (eq_vec (B4 !!! Regidx (mword_of_int 13 : mword 5))
                     (B4 !!! Regidx (mword_of_int 14 : mword 5))) eqn:Hbeq.
    2:{ (* the V&U test fails: fall into the epilogue with a0 = 0 *)
        iApply (wp_beq_fall_s_sconf γ Φ (mword_of_int (WA + 0x26)) (mword_of_int 12 : mword 13)
                  (mword_of_int 14 : mword 5) (mword_of_int 13 : mword 5) B4 (K - 2)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbeq
                  with "Hcg Hpc Hi26 [-]").
        iIntros "Hcg Hpc".
        assert (Hpp2a : add_vec_int (mword_of_int (WA + 0x26) : mword 64) 4
                        = mword_of_int (WA + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp2a) in "Hpc".
        iApply ("EPI" $! B4 with "[%] Hcg Hpc Hptree [%]").
        { exact HcsB4. }
        { left. exact HB4a0. } }
    (* ---- V and U are both set: this vpn IS mapped, and PTE2PA is the answer ---- *)
    assert (Hand : and_vec w0 (sign_extend' 64 (mword_of_int 17 : mword 12))
                   = (mword_of_int 17 : mword 64)).
    { apply eq_vec_true_iff in Hbeq. rewrite HB4a3 HB4a4 in Hbeq. exact Hbeq. }
    assert (Hvu : pte_vu w0) by (apply pte_vu_bits; exact Hand).
    assert (Hsome : m !! vpn = Some w0).
    { destruct Hverd as [Hs | (Hw0z & _)]; [exact Hs | exfalso].
      rewrite Hw0z in Hand. apply (f_equal bv_unsigned) in Hand.
      vm_compute in Hand. discriminate. }
    (* the leaf word is a model-valid 4K leaf, so its ten extension bits are
       clear -- which is what makes [srli 10; slli 12] equal [page_base]. *)
    assert (Hlt54 : bv_unsigned w0 < 18014398509481984).
    { destruct Hrep as (Hmaps & _).
      destruct (Hmaps vpn w0 Hsome) as (q2 & q1 & Hmp).
      destruct Hmp as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                        & Hv0 & _ & Hnn & Hpb).
      exact (pte_hi_zero w0 Hv0 Hnn Hpb). }
    iPoseProof (wai_32 with "Htext") as "Hi32".
    iPoseProof (wai_34 with "Htext") as "Hi34".
    iPoseProof (wai_38 with "Htext") as "Hi38".
    iApply (wp_beq_taken_s_sconf γ Φ (mword_of_int (WA + 0x26)) (mword_of_int 12 : mword 13)
              (mword_of_int 14 : mword 5) (mword_of_int 13 : mword 5) B4 (K - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbeq
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi26 [-]").
    iNext. iIntros "Hcg Hpc".
    assert (Htgt32 : add_vec (mword_of_int (WA + 0x26) : mword 64)
              (sign_extend' 64 (mword_of_int 12 : mword 13)) = mword_of_int (WA + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt32) in "Hpc".
    (* +0x32 c.srli a5,a5,0xa *)
    iApply (wp_csrli_s_sconf γ Φ (mword_of_int (WA + 0x32)) (Cregidx (mword_of_int 7))
              (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 6) B4 (K - 2)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi32 [-]").
    iIntros "Hcg Hpc".
    set (B5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (B4 !!! Regidx (mword_of_int 15 : mword 5))
           (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> B4).
    assert (HB5a5 : B5 !!! Regidx (mword_of_int 15 : mword 5)
                    = shift_bits_right w0
                        (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0)).
    { rewrite /B5 upd_eq. rewrite HB4a5. reflexivity. }
    assert (Hpp34 : add_vec_int (mword_of_int (WA + 0x32) : mword 64) 2
                    = mword_of_int (WA + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* +0x34 slli a0,a5,0xc : PTE2PA *)
    assert (Hs10 : int_of_mword false
              (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0) = 10)
      by (vm_compute; reflexivity).
    assert (Hs12 : int_of_mword false
              (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0) = 12)
      by (vm_compute; reflexivity).
    assert (Hpte2pa : shift_bits_left (B5 !!! Regidx (mword_of_int 15 : mword 5))
              (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
            = page_base (pte_ppn w0)).
    { rewrite HB5a5. apply pte2pa; [ exact Hs10 | exact Hs12 | exact Hlt54 ]. }
    iApply (wp_slli_s_sconf γ Φ (mword_of_int (WA + 0x34)) (mword_of_int 10 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 12 : mword 6)
              (page_base (pte_ppn w0)) B5 (K - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hpte2pa
              with "Hcg Hpc Hi34 [-]").
    iIntros "Hcg Hpc".
    set (B6 := <[Regidx (mword_of_int 10 : mword 5) :=
        regval_into_reg (page_base (pte_ppn w0))]> B5).
    assert (HB6a0 : B6 !!! Regidx (mword_of_int 10 : mword 5) = page_base (pte_ppn w0))
      by (rewrite /B6 upd_eq; reflexivity).
    assert (HcsB6 : callee_saved mw B6).
    { rewrite /B6. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /B5. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      exact HcsB4. }
    assert (Hpp38 : add_vec_int (mword_of_int (WA + 0x34) : mword 64) 4
                    = mword_of_int (WA + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    (* +0x38 c.j -0x0e : back to the epilogue *)
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (WA + 0x38))
              (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")))
              B6 (K - 2)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi38 [-]").
    iNext. iIntros "Hcg Hpc".
    assert (Htgt2a' : add_vec (mword_of_int (WA + 0x38) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0"))))
            = mword_of_int (WA + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt2a') in "Hpc".
    iApply ("EPI" $! B6 with "[%] Hcg Hpc Hptree [%]").
    { exact HcsB6. }
    { right. exists w0. split; [exact Hsome |]. split; [exact Hvu | exact HB6a0]. }
  Qed.

End ProofWalkaddr.

End WalkaddrProof.
