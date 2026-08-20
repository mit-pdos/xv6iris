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
     arm consumes and restores it).  Under explicit-cpuid this join point
     (EPI, below) is reached from THREE independently-abstract harts (its
     three call sites each specialize their OWN wp_next-bound CID), so EPI
     itself has to be generic over its entry hart and carry the caller's
     accumulated wp_next chain as an explicit premise -- see the comment at
     its definition;
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
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import HartTp WpNext IntrDefs WpSmodeIntr.
Require Import CommonWalk PtTree.
Require Import KptTree.   (* pt_slot_phys_to_mem / pt_slot_mem_to_phys *)
Require Import PtBuild.
Require Import ProcPtOwn.
Require Import CodeWalkaddr.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecWalk.
Require Import SpecWalkaddr.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
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

(* ...and the same test's OTHER verdict, which the informative failure arm
   now has to report. *)
Lemma wa_z_maxva_ge (x : Z) : Z.geb 274877906943 x = false -> 2 ^ 38 <= x.
Proof.
  intros H. rewrite Z.geb_leb in H. apply Z.leb_gt in H.
  assert (P : 2 ^ 38 = 274877906944) by (vm_compute; reflexivity).
  rewrite P. lia.
Qed.


(* ===================================================================== *)
(* THE V&U BIT TEST, THE DIRECTION [PtBuild.pte_vu_bits] DOES NOT PROVE.   *)
(*                                                                        *)
(*   [pte_vu_bits] reads the TAKEN [beq]: the mask came out 17, so V and  *)
(*   U are both set.  The failure arm reports [~ pte_vu w], so it needs    *)
(*   the converse -- if V and U are both set the mask MUST come out 17.    *)
(*   The proper home is beside [pte_vu_bits] in PtBuild.v (with the three  *)
(*   field extractions, which are [Local] there and so are restated here); *)
(*   kept local only to avoid a mid-tree recompile.                        *)
(* ===================================================================== *)
Local Lemma wa_sub_7_0 (v : mword 64) :
  bv_unsigned (subrange_vec_dec v 7 0 : mword 8) = bv_unsigned v mod 256.
Proof. apply (subrange_dec_unsigned_lo0 v 7 256); [lia | reflexivity]. Qed.

Local Lemma wa_sub_0_0 (v : mword 8) :
  bv_unsigned (subrange_vec_dec v 0 0 : mword 1) = bv_unsigned v mod 2.
Proof. apply (subrange_dec_unsigned_lo0 v 0 2); [lia | reflexivity]. Qed.

Local Lemma wa_sub_4_4 (v : mword 8) :
  bv_unsigned (subrange_vec_dec v 4 4 : mword 1) = bv_unsigned v / 16 mod 2.
Proof. apply (subrange_dec_unsigned v 4 4 16 2); [lia | lia | reflexivity | reflexivity]. Qed.

Local Lemma wa_z_mod_to_bit (y : Z) : y mod 2 = 1 -> Z.testbit y 0 = true.
Proof.
  intros H. rewrite Z.bit0_odd. rewrite Zmod_odd in H.
  destruct (Z.odd y); [reflexivity | discriminate].
Qed.

(* 17 is exactly bits 0 and 4 *)
Local Lemma wa_bit17 (n : Z) : 0 <= n -> n <> 0 -> n <> 4 -> Z.testbit 17 n = false.
Proof.
  intros Hn H0 H4.
  destruct (Z_lt_le_dec n 5) as [Hlt | Hge].
  - assert (Hc : n = 1 \/ n = 2 \/ n = 3) by lia.
    destruct Hc as [-> | [-> | ->]]; vm_compute; reflexivity.
  - apply Z.bits_above_log2; [lia |].
    assert (Hl : Z.log2 17 = 4) by (vm_compute; reflexivity). lia.
Qed.

Lemma wa_pte_vu_bits_inv (w : mword 64) :
  pte_vu w ->
  and_vec w (sign_extend' 64 (mword_of_int 17 : mword 12)) = (mword_of_int 17 : mword 64).
Proof.
  intros (HV & HU).
  unfold _get_PTE_Flags_V, _get_PTE_Flags_U, Mk_PTE_Flags in HV, HU.
  apply (f_equal bv_unsigned) in HV. apply (f_equal bv_unsigned) in HU.
  assert (H1 : bv_unsigned ('b"1" : mword 1) = 1) by (vm_compute; reflexivity).
  rewrite H1 in HV. rewrite H1 in HU.
  rewrite wa_sub_0_0 wa_sub_7_0 in HV.
  rewrite wa_sub_4_4 wa_sub_7_0 in HU.
  assert (Hb0 : Z.testbit (bv_unsigned w) 0 = true).
  { apply wa_z_mod_to_bit in HV.
    change 256 with (2 ^ 8) in HV.
    rewrite Z.mod_pow2_bits_low in HV; [exact HV | lia]. }
  assert (Hb4 : Z.testbit (bv_unsigned w) 4 = true).
  { apply wa_z_mod_to_bit in HU.
    change 16 with (2 ^ 4) in HU.
    rewrite Z.div_pow2_bits in HU; [| lia | lia].
    change 256 with (2 ^ 8) in HU.
    rewrite Z.mod_pow2_bits_low in HU; [| lia].
    replace (0 + 4) with 4 in HU by lia. exact HU. }
  apply bv_eq. rewrite andi17_unsigned.
  assert (H17 : bv_unsigned (mword_of_int 17 : mword 64) = 17)
    by (vm_compute; reflexivity).
  rewrite H17.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.eq_dec n 0) as [-> | Hn0]; [rewrite Hb0; reflexivity |].
  destruct (Z.eq_dec n 4) as [-> | Hn4]; [rewrite Hb4; reflexivity |].
  rewrite (wa_bit17 n Hn Hn0 Hn4). apply andb_false_r.
Qed.

(* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]) -- the
   one-line bridge from a leaf's [rget] to the register-map facts a
   whole-function proof already has.  Written name-free (durable-notes: an
   Ltac body cannot mention a hypothesis by literal name). *)
Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].


(* ===================================================================== *)
(* THE WHOLE FUNCTION.                                                    *)
(* ===================================================================== *)

Module WalkaddrProof (WalkNoalloc : WALK_NOALLOC) : WALKADDR.

Section ProofWalkaddr.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_walkaddr_sconf (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (K : nat) (dq : dfrac) (b : bool) (p : mword 64)
    : wp_walkaddr_sconf_body mm t m K dq b p.
  Proof.
    cbv beta delta [wp_walkaddr_sconf_body].
    intros pcE va vpn ret_tgt HK Hroot Hrep.
    iIntros "Hcg #Htext Hpc Hptree Hcont".
    iPoseProof (wai_00 with "Htext") as "Hi00".
    iPoseProof (wai_02 with "Htext") as "Hi02".
    iPoseProof (wai_04 with "Htext") as "Hi04".
    (* ---- +0x00 c.li a5,-1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int KernelSyms.walkaddr) (mword_of_int 15 : mword 5)
              (mword_of_int 63 : mword 6) (mword_of_int 18446744073709551615 : mword 64) mm K b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (V1 := <[Regidx (mword_of_int 15 : mword 5) :=
        regval_into_reg (mword_of_int 18446744073709551615 : mword 64)]> mm).
    assert (Hpp02 : add_vec_int (mword_of_int KernelSyms.walkaddr : mword 64) 2 = mword_of_int (KernelSyms.walkaddr + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* ---- +0x02 c.srli a5,a5,0x1a : a5 := 2^38 - 1 ---- *)
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x02)) (Cregidx (mword_of_int 7))
              (mword_of_int 15 : mword 5) (mword_of_int 26 : mword 6) V1 K b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi02").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (V2 := <[Regidx (mword_of_int 15 : mword 5) :=
        regval_into_reg (mword_of_int 274877906943 : mword 64)]> mm).
    assert (HV2c : <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (rget (CID := CID1) V1 (mword_of_int 15 : mword 5))
           (subrange_vec_dec (mword_of_int 26 : mword 6) (Z.sub log2_xlen 1) 0))]> V1 = V2).
    { rgne. rewrite /V2 /V1 upd_upd. do 2 f_equal. rewrite upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite HV2c) in "Hcg".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.walkaddr + 0x04))
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
    (* the rget-bridged version of [Hcmp], built BEFORE the destruct so that
       it (like [Hcmp] itself) auto-narrows to [=false]/[=true] in each
       branch -- confirmed: [destruct t eqn:H] DOES rewrite every local
       hypothesis mentioning the exact scrutinee [t], not just the goal. *)
    assert (Hcmpg : zopz0zKzJ_u (rget (CID := CID2) V2 (mword_of_int 15 : mword 5))
                      (rget (CID := CID2) V2 (mword_of_int 11 : mword 5))
                    = Z.geb 274877906943 (uint va)).
    { rgne. rgne. exact Hcmp. }
    (* ================================================================= *)
    (* +0x04 bgeu a5,a1 : the MAXVA test.  The FALL-THROUGH arm returns 0 *)
    (* at +0x0a without ever pushing a frame.                             *)
    (* ================================================================= *)
    destruct (Z.geb 274877906943 (uint va)) eqn:Hge.
    2:{ iPoseProof (wai_08 with "Htext") as "Hi08".
        iPoseProof (wai_0a with "Htext") as "Hi0a".
        iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x04)) (mword_of_int 8 : mword 13)
                  (mword_of_int 11 : mword 5) (mword_of_int 15 : mword 5) V2 K b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmpg
                  with "Hcg Hpc Hi04").
        iIntros (CID3 Hs3) "Hcg Hpc".
        assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x04) : mword 64) 4
                        = mword_of_int (KernelSyms.walkaddr + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp08) in "Hpc".
        (* +0x08 c.li a0,0 *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x08)) (mword_of_int 10 : mword 5)
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) V2 K b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi08").
        iIntros (CID4 Hs4) "Hcg Hpc".
        set (V3 := <[Regidx (mword_of_int 10 : mword 5) :=
            regval_into_reg (mword_of_int 0 : mword 64)]> V2).
        assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x08) : mword 64) 2
                        = mword_of_int (KernelSyms.walkaddr + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp0a) in "Hpc".
        assert (HV3ra : V3 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
        { rewrite /V3. rewrite upd_ne; [| vm_compute; discriminate].
          rewrite /V2. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
        assert (Hrt : ret_pc (V3 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
          by (rewrite HV3ra; reflexivity).
        assert (Hrtg : ret_pc (rget (CID := CID4) V3 (mword_of_int 1 : mword 5)) = ret_tgt)
          by (rgne; exact Hrt).
        (* +0x0a c.ret *)
        iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x0a)) (mword_of_int 1 : mword 5) V3 K b
                  ltac:(vm_compute; discriminate) with "Hcg Hpc Hi0a").
        iIntros (CID5 Hs5) "Hcg Hpc".
        iEval (rewrite Hrtg) in "Hpc".
        iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! V3 with "Hcg Hpc Hptree [%] [%]").
        { rewrite /V3. apply callee_saved_insert_r; [vm_compute; reflexivity |].
          rewrite /V2. apply callee_saved_insert_r; [vm_compute; reflexivity |].
          apply callee_saved_refl. }
        { left. split; [rewrite /V3 upd_eq; reflexivity |].
          left. exact (wa_z_maxva_ge (uint va) Hge). } }
    (* ---- va < MAXVA: the branch is TAKEN, into the framed body ------- *)
    assert (Hvalt : (uint va < 2 ^ 38)%Z) by (apply wa_z_maxva; exact Hge).
    iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x04)) (mword_of_int 8 : mword 13)
              (mword_of_int 11 : mword 5) (mword_of_int 15 : mword 5) V2 K b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Hcmpg ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi04").
    iNext. iIntros (CID6 Hs6) "Hcg Hpc".
    assert (Htgt0c : add_vec (mword_of_int (KernelSyms.walkaddr + 0x04) : mword 64)
              (sign_extend' 64 (mword_of_int 8 : mword 13)) = mword_of_int (KernelSyms.walkaddr + 0x0c))
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
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x0c)) (mword_of_int 48 : mword 6)
              V2 K 2 b ltac:(lia) Hpush with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (V2 !!! Regidx csp_rs1)
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> V2) with W1.
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v8) "Hc1". iDestruct "S2" as (v0) "Hc2".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr) by (rewrite /W1 upd_eq; reflexivity).
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.walkaddr + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x0e)) (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 5) W1 (K - 2)%nat v8 b with "Hcg Hpc Hi0e [Hc1]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros (CID8 Hs8) "Hcg Hpc Hc1".
    iEval (rewrite HspW1 Hb1) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /W1. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /V2. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HW1r1g : rget (CID := CID7) W1 (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1))
      by (rgne; exact HW1r1).
    iEval (rewrite HW1r1g) in "Hc1".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.walkaddr + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x10)) (mword_of_int 0 : mword 6)
              (mword_of_int 8 : mword 5) W1 (K - 2)%nat v0 b with "Hcg Hpc Hi10 [Hc2]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros (CID9 Hs9) "Hcg Hpc Hc2".
    iEval (rewrite HspW1 Hb2) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
    { rewrite /W1. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /V2. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HW1r8g : rget (CID := CID8) W1 (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8))
      by (rgne; exact HW1r8).
    iEval (rewrite HW1r8g) in "Hc2".
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x10) : mword 64) 2
                    = mword_of_int (KernelSyms.walkaddr + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x12)) (Cregidx (mword_of_int 0))
              (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5) W1 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi12").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x12) : mword 64) 2
                    = mword_of_int (KernelSyms.walkaddr + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.li a2,0 (walk's alloc argument) *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x14)) (mword_of_int 12 : mword 5)
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) W2 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi14").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (W3 := <[Regidx (mword_of_int 12 : mword 5) :=
        regval_into_reg (mword_of_int 0 : mword 64)]> W2).
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x14) : mword 64) 2
                    = mword_of_int (KernelSyms.walkaddr + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 jal ra,walk *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x16)) (mword_of_int 1 : mword 5)
              (mword_of_int 2096976 : mword 21) W3 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi16").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (W4 := <[Regidx (mword_of_int 1 : mword 5) :=
        regval_into_reg (add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x16) : mword 64) 4)]> W3).
    assert (Hpcwk : add_vec (mword_of_int (KernelSyms.walkaddr + 0x16) : mword 64)
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
                    = add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x16) : mword 64) 4)
      by (rewrite /W4 upd_eq; reflexivity).
    assert (Hret1a : ret_pc (W4 !!! Regidx (mword_of_int 1 : mword 5))
                     = mword_of_int (KernelSyms.walkaddr + 0x1a)).
    { rewrite HW4ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    assert (Hwkva : (uint (W4 !!! Regidx (mword_of_int 11 : mword 5)) < 2 ^ 38)%Z)
      by (rewrite HW4a1; exact Hvalt).
    assert (HKw : (8 <= K - 2)%nat) by lia.
    (* ---- the call ---- *)
    iApply (WalkNoalloc.wp_walk_noalloc_sconf KT1 W4 t m (K - 2)%nat dq b p
              HKw HW4a0 HW4a2 Hwkva Hrep
              with "Hcg Htext Hpc Hptree").
    iIntros (CID13 Hs13 mw) "Hcg Hpc Hptree %Hkcs %Hpay".
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
    (*                                                                     *)
    (* EPI is shared by THREE call sites (the walk-NULL arm, the V&U-fail  *)
    (* arm, and the V&U-ok arm), each of which reaches it at its OWN,      *)
    (* independently-abstract wp_next-bound hart -- unlike every other     *)
    (* join point in this proof, EPI must therefore be GENERIC over its    *)
    (* entry hart [CIDe], carrying the caller's own accumulated wp_next    *)
    (* chain as an explicit premise [Hchain] (shape [b=false -> CIDe=CID], *)
    (* exactly what a leaf's own [wp_next] would hand a continuation) so   *)
    (* that EPI's internal steps (CID14..CID17) can be composed back to    *)
    (* the function's entry hart at the final [Hcont] discharge, via the   *)
    (* SAME [wp_next_chain] congruence closer used everywhere else -- it   *)
    (* is blind to WHERE a [_ = false -> _ = _] hypothesis came from.      *)
    (* ================================================================= *)
    iAssert (∀ (CIDe : CpuId) (M : regfile),
               ⌜b = false \/ p = zero_reg -> (CIDe : CPU) = (CID : CPU)⌝ -∗
               ⌜callee_saved mw M⌝ -∗
               sie_cap_gpr KT1 (CID := CIDe) M (K - 2)%nat b p -∗
               pc_is (CID := CIDe) (mword_of_int (KernelSyms.walkaddr + 0x2a) : mword 64) -∗
               ptree_own 2 dq t -∗
               ⌜ (M !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0 /\
                    ((2 ^ 38 <= uint va)%Z
                     \/ m !! vpn = None
                     \/ (exists w, m !! vpn = Some w /\ ~ pte_vu w)))
                 \/ (exists w, m !! vpn = Some w /\ pte_vu w /\
                       M !!! Regidx (mword_of_int 10 : mword 5) = page_base (pte_ppn w)) ⌝ -∗
               WP (Loop : expr riscv_lang))%I
      with "[Hcont Hc1 Hc2]" as "EPI".
    { iIntros (CIDe M) "%Hchain %HcsM Hcg Hpc Hptree %Hpay'".
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
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x2a)) (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 5) M (K - 2)%nat (mm !!! Regidx (mword_of_int 1)) b
                (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2a [Hc1]").
      { iEval (rewrite HspM Hb1). iExact "Hc1". }
      iIntros (CID14 Hs14) "Hcg Hpc Hc1".
      iEval (rewrite HspM Hb1) in "Hc1".
      set (E1 := <[Regidx (mword_of_int 1 : mword 5) :=
          regval_into_reg (mm !!! Regidx (mword_of_int 1))]> M).
      assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x2a) : mword 64) 2
                      = mword_of_int (KernelSyms.walkaddr + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2c) in "Hpc".
      (* +0x2c c.ldsp s0,0(sp) *)
      assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
      { rewrite /E1. rewrite upd_ne; [| vm_compute; discriminate]. exact HspM. }
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x2c)) (mword_of_int 0 : mword 6)
                (mword_of_int 8 : mword 5) E1 (K - 2)%nat (mm !!! Regidx (mword_of_int 8)) b
                (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2c [Hc2]").
      { iEval (rewrite HspE1 Hb2). iExact "Hc2". }
      iIntros (CID15 Hs15) "Hcg Hpc Hc2".
      iEval (rewrite HspE1 Hb2) in "Hc2".
      set (E2 := <[Regidx (mword_of_int 8 : mword 5) :=
          regval_into_reg (mm !!! Regidx (mword_of_int 8))]> E1).
      assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x2c) : mword 64) 2
                      = mword_of_int (KernelSyms.walkaddr + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
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
      iAssert (stack_own (KTR := KT1) sp0 2) with "[Hc1 Hc2]" as "Hfr".
      { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
        iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
        iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
        done. }
      iEval (rewrite -Hwv) in "Hfr".
      iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x2e)) (mword_of_int 16 : mword 6)
                E2 (K - 2)%nat 2 b Hpop with "Hcg Hpc Hi2e Hfr").
      iIntros (CID16 Hs16) "Hcg Hpc".
      change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1)
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2) with E3.
      assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x2e) : mword 64) 2
                      = mword_of_int (KernelSyms.walkaddr + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
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
      assert (Hrtg : ret_pc (rget (CID := CID16) E3 (mword_of_int 1 : mword 5)) = ret_tgt)
        by (rgne; exact Hrt).
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x30)) (mword_of_int 1 : mword 5) E3 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hi30").
      iIntros (CID17 Hs17) "Hcg Hpc".
      iEval (rewrite Hrtg) in "Hpc".
      iSpecialize ("Hcont" $! CID17 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! E3 with "Hcg Hpc Hptree [%] [%]").
      { unfold callee_saved. split_and!.
        - rewrite HspE3. rewrite /sp0 /V2.
          rewrite upd_ne; [reflexivity | vm_compute; discriminate].
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
      { rewrite HE3a0. destruct Hpay' as [(Hz & Hwhy) | (w & Hsome & Hvu & Ha0)].
        - left. split; [exact Hz | exact Hwhy].
        - right. exists w. split; [exact Hsome |]. split; [exact Hvu |].
          split; [exact Hvalt | exact Ha0]. } }
    (* ================================================================= *)
    (* +0x1a c.beqz a0 : the walk verdict.                                *)
    (* ================================================================= *)
    iPoseProof (wai_1a with "Htext") as "Hi1a".
    destruct Hpay as [(Ha0z & Hnone) | (p2 & p1 & w0 & Hl0 & Ha0v & Hverd)].
    { (* ---- walk returned NULL: branch TAKEN, a0 = 0 already ---- *)
      assert (Ha0zg : eq_vec (rget (CID := CID13) mw (mword_of_int 10 : mword 5)) zero_reg = true)
        by (rgne; rewrite Ha0z; vm_compute; reflexivity).
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x1a)) (mword_of_int 8 : mword 8)
                (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5) mw (K - 2)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                Ha0zg
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1a").
      iNext. iIntros (CID18 Hs18) "Hcg Hpc".
      assert (Htgt2a : add_vec (mword_of_int (KernelSyms.walkaddr + 0x1a) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 8 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.walkaddr + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt2a) in "Hpc".
      iApply ("EPI" $! CID18 mw with "[%] [%] Hcg Hpc Hptree [%]").
      { wp_next_chain. }
      { apply callee_saved_refl. }
      { left. split; [exact Ha0z |]. right. left. exact Hnone. } }
    (* ---- walk returned the L0 slot address: read it ---- *)
    iDestruct (ptree_own_level0_ro dq t vpn p2 p1 w0 Hl0 with "Hptree") as "(#Hcl0 & Hcell & Hclose)".
    iDestruct (phys_word_pointsto_ram with "Hcell") as %Hslotram.
    iDestruct (pt_slot_phys_to_mem (u_next_base p1) (vpn_idx 0 vpn) dq w0
                 with "Hcl0 Hcell") as "Hcell".
    assert (Ha0nz : mw !!! Regidx (mword_of_int 10 : mword 5) <> mword_of_int 0).
    { rewrite Ha0v. intro Heq. rewrite Heq in Hslotram.
      unfold addr_is_ram in Hslotram. destruct Hslotram as [Hlo _].
      apply (proj2 (Z.leb_le _ _)) in Hlo. vm_compute in Hlo. discriminate. }
    assert (Ha0nzg : eq_vec (rget (CID := CID13) mw (mword_of_int 10 : mword 5)) zero_reg = false).
    { rgne. apply eq_vec_false_iff. intro He. apply Ha0nz.
      rewrite He. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (wai_1c with "Htext") as "Hi1c".
    iPoseProof (wai_1e with "Htext") as "Hi1e".
    iPoseProof (wai_22 with "Htext") as "Hi22".
    iPoseProof (wai_24 with "Htext") as "Hi24".
    iPoseProof (wai_26 with "Htext") as "Hi26".
    (* +0x1a c.beqz a0 FALLS *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x1a)) (mword_of_int 8 : mword 8)
              (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5) mw (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              Ha0nzg
              with "Hcg Hpc Hi1a").
    iIntros (CID19 Hs19) "Hcg Hpc".
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x1a) : mword 64) 2
                    = mword_of_int (KernelSyms.walkaddr + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.ld a5,0(a0) *)
    assert (Hea0 : forall X : mword 64,
        add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    assert (Ha0vg : rget (CID := CID19) mw (mword_of_int 10 : mword 5) = pt_addr0 p1 vpn)
      by (rgne; exact Ha0v).
    iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.walkaddr + 0x1c)) (mword_of_int 15 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 0 : mword 12)
              mw (K - 2)%nat w0 b (dqm:=dq)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [Hcell]").
    { iEval (rewrite Hea0 Ha0vg). iExact "Hcell". }
    iIntros (CID20 Hs20) "Hcg Hpc Hcell".
    iEval (rewrite Hea0 Ha0vg) in "Hcell".
    set (B1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w0]> mw).
    assert (HB1a5 : B1 !!! Regidx (mword_of_int 15 : mword 5) = w0)
      by (rewrite /B1 upd_eq; reflexivity).
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.walkaddr + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* give the tree back: the slot is untouched *)
    iDestruct (pt_slot_mem_to_phys (u_next_base p1) (vpn_idx 0 vpn) dq w0
                 with "Hcl0 Hcell") as "Hcell".
    iDestruct ("Hclose" with "Hcell") as "Hptree".
    (* +0x1e andi a3,a5,17 *)
    assert (HB1a5g : and_vec (rget (CID := CID20) B1 (mword_of_int 15 : mword 5))
                       (sign_extend' 64 (mword_of_int 17 : mword 12))
                     = and_vec w0 (sign_extend' 64 (mword_of_int 17 : mword 12)))
      by (rgne; rewrite HB1a5; reflexivity).
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x1e)) (mword_of_int 13 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 17 : mword 12)
              (and_vec w0 (sign_extend' 64 (mword_of_int 17 : mword 12))) B1 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              HB1a5g
              with "Hcg Hpc Hi1e").
    iIntros (CID21 Hs21) "Hcg Hpc".
    set (B2 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg
        (and_vec w0 (sign_extend' 64 (mword_of_int 17 : mword 12)))]> B1).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x1e) : mword 64) 4
                    = mword_of_int (KernelSyms.walkaddr + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 c.li a4,17 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x22)) (mword_of_int 14 : mword 5)
              (mword_of_int 17 : mword 6) (mword_of_int 17 : mword 64) B2 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi22").
    iIntros (CID22 Hs22) "Hcg Hpc".
    set (B3 := <[Regidx (mword_of_int 14 : mword 5) :=
        regval_into_reg (mword_of_int 17 : mword 64)]> B2).
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.walkaddr + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* +0x24 c.li a0,0 : the 0 return, set before the test *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x24)) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) B3 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi24").
    iIntros (CID23 Hs23) "Hcg Hpc".
    set (B4 := <[Regidx (mword_of_int 10 : mword 5) :=
        regval_into_reg (mword_of_int 0 : mword 64)]> B3).
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x24) : mword 64) 2
                    = mword_of_int (KernelSyms.walkaddr + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
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
        assert (Hbeqg : eq_vec (rget (CID := CID23) B4 (mword_of_int 13 : mword 5))
                          (rget (CID := CID23) B4 (mword_of_int 14 : mword 5)) = false)
          by (rgne; rgne; exact Hbeq).
        iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x26)) (mword_of_int 12 : mword 13)
                  (mword_of_int 14 : mword 5) (mword_of_int 13 : mword 5) B4 (K - 2)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbeqg
                  with "Hcg Hpc Hi26").
        iIntros (CID24 Hs24) "Hcg Hpc".
        assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x26) : mword 64) 4
                        = mword_of_int (KernelSyms.walkaddr + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp2a) in "Hpc".
        iApply ("EPI" $! CID24 B4 with "[%] [%] Hcg Hpc Hptree [%]").
        { wp_next_chain. }
        { exact HcsB4. }
        (* the reason: either the slot was the zero word (so this vpn is not
           in the map at all) or it is in the map and its V&U test failed *)
        { left. split; [exact HB4a0 |]. right.
          apply eq_vec_false_iff in Hbeq. rewrite HB4a3 HB4a4 in Hbeq.
          destruct Hverd as [Hs | (_ & Hn)].
          - right. exists w0. split; [exact Hs |].
            intro Hvu. exact (Hbeq (wa_pte_vu_bits_inv w0 Hvu)).
          - left. exact Hn. } }
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
    assert (Hbeqg' : eq_vec (rget (CID := CID23) B4 (mword_of_int 13 : mword 5))
                       (rget (CID := CID23) B4 (mword_of_int 14 : mword 5)) = true)
      by (rgne; rgne; exact Hbeq).
    iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x26)) (mword_of_int 12 : mword 13)
              (mword_of_int 14 : mword 5) (mword_of_int 13 : mword 5) B4 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbeqg'
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi26").
    iNext. iIntros (CID25 Hs25) "Hcg Hpc".
    assert (Htgt32 : add_vec (mword_of_int (KernelSyms.walkaddr + 0x26) : mword 64)
              (sign_extend' 64 (mword_of_int 12 : mword 13)) = mword_of_int (KernelSyms.walkaddr + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt32) in "Hpc".
    (* +0x32 c.srli a5,a5,0xa *)
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x32)) (Cregidx (mword_of_int 7))
              (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 6) B4 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi32").
    iIntros (CID26 Hs26) "Hcg Hpc".
    set (B5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (B4 !!! Regidx (mword_of_int 15 : mword 5))
           (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> B4).
    assert (HB4c : <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (rget (CID := CID25) B4 (mword_of_int 15 : mword 5))
           (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> B4 = B5).
    { rgne. reflexivity. }
    iEval (rewrite HB4c) in "Hcg".
    assert (HB5a5 : B5 !!! Regidx (mword_of_int 15 : mword 5)
                    = shift_bits_right w0
                        (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0)).
    { rewrite /B5 upd_eq. rewrite HB4a5. reflexivity. }
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x32) : mword 64) 2
                    = mword_of_int (KernelSyms.walkaddr + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* +0x34 slli a0,a5,0xc : PTE2PA *)
    assert (Hsh10 : int_of_mword false
              (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0) = 10)
      by (vm_compute; reflexivity).
    assert (Hsh12 : int_of_mword false
              (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0) = 12)
      by (vm_compute; reflexivity).
    assert (Hpte2pa : shift_bits_left (B5 !!! Regidx (mword_of_int 15 : mword 5))
              (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
            = page_base (pte_ppn w0)).
    { rewrite HB5a5. apply pte2pa; [ exact Hsh10 | exact Hsh12 | exact Hlt54 ]. }
    assert (Hpte2pag : shift_bits_left (rget (CID := CID26) B5 (mword_of_int 15 : mword 5))
              (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
            = page_base (pte_ppn w0))
      by (rgne; exact Hpte2pa).
    iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x34)) (mword_of_int 10 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 12 : mword 6)
              (page_base (pte_ppn w0)) B5 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) Hpte2pag
              with "Hcg Hpc Hi34").
    iIntros (CID27 Hs27) "Hcg Hpc".
    set (B6 := <[Regidx (mword_of_int 10 : mword 5) :=
        regval_into_reg (page_base (pte_ppn w0))]> B5).
    assert (HB6a0 : B6 !!! Regidx (mword_of_int 10 : mword 5) = page_base (pte_ppn w0))
      by (rewrite /B6 upd_eq; reflexivity).
    assert (HcsB6 : callee_saved mw B6).
    { rewrite /B6. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /B5. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      exact HcsB4. }
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.walkaddr + 0x34) : mword 64) 4
                    = mword_of_int (KernelSyms.walkaddr + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    (* +0x38 c.j -0x0e : back to the epilogue *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.walkaddr + 0x38))
              (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")))
              B6 (K - 2)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi38").
    iIntros (CID28 Hs28). iNext. iIntros "Hcg Hpc".
    assert (Htgt2a' : add_vec (mword_of_int (KernelSyms.walkaddr + 0x38) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.walkaddr + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt2a') in "Hpc".
    iApply ("EPI" $! CID28 B6 with "[%] [%] Hcg Hpc Hptree [%]").
    { wp_next_chain. }
    { exact HcsB6. }
    { right. exists w0. split; [exact Hsome |]. split; [exact Hvu | exact HB6a0]. }
  Qed.

End ProofWalkaddr.

End WalkaddrProof.
