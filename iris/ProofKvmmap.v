(* ProofKvmmap.v -- kvmmap() over the SIE-agnostic sconf world.
   Mirror of the smode wp_kvmmap_r (CodeKvmmap.v): a thin 2-slot-frame wrapper
   that calls mappages() once (panicking on failure).  Threads the same sconf
   bundle + ptree_own + kalloc_env as mappages.

   NOTE (WIP): the SPEC below is walk-independent and typechecks now; the PROOF
   composes Mappages.wp_mappages_sconf (ProofMappages.v) is filled once the walk +
   mappages ports land. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import PanicStub.
Require Import RegFile.
Require Import WpLock WpMmodeLeafBase.
Require Import CalleeSaved StackOwn.
Require Import KallocInv.
Require Import PtreeType.
Require Import Riscv.riscv_extras.
Require Import CodeKvmmap.
Require Import SpecMappages.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecKvmmap.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.

Module KvmmapProof (Mappages : MAPPAGES) : KVMMAP.

Section ProofKvmmap.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Lemma wp_kvmmap_sconf
      (γa : gname)
      (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (npages : nat) (perm : Z) (lvl K : nat)
      (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string)
    : wp_kvmmap_sconf_body γa mm t m npages perm lvl K eb p on b lks.
  Proof.
    cbv beta delta [wp_kvmmap_sconf_body].
    intros va pa vpn0 ppn0 ret_tgt
      Hlvl HK Hroot Hvaal Hpaal Hsz Hnp Hpermreg Hpok Hvab Hpab Hrep Hnone Hex Hlkbelow.
    destruct Hex as (nb & Hon & Hnbk). subst on.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    assert (Hsp1 : W1 !!! Regidx csp_rs1 = pa_stk (mm !!! Regidx csp_rs1) 2).
    { rewrite /W1 upd_eq. unfold regval_into_reg, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    iIntros "Hcg Hcnt #Htext Hpc Hptree Henv Hcont".
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
    (* +0x00 c.addi sp,-16 : the 2-slot frame push *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int KernelSyms.kvmmap) (mword_of_int 48 : mword 6) mm K 2 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm) with W1.
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v8) "Hc1". iDestruct "S2" as (v0) "Hc2".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr)
      by (rewrite /W1 upd_eq; reflexivity).
    assert (Hpp02 : add_vec_int (mword_of_int KernelSyms.kvmmap : mword 64) 2 = mword_of_int (KernelSyms.kvmmap + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kvmmap + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 2)%nat v8 b with "Hcg Hpc Hi02 [Hc1]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1".
    iEval (rewrite HspW1 Hb1) in "Hc1".
    (* the leaf's [storeval] is [rget m rs2], let-bound OUTSIDE its own
       [wp_next] lambda -- it is read at the CALLER's ambient hart (CID1,
       active when this leaf was applied), not at CID2. [rgne] peels that
       [rget] down to the CID-free [!!!] lookup before the plain map-chain
       fact [HW1r1] can rewrite it. *)
    iEval (rgne) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r1) in "Hc1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.kvmmap + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.kvmmap + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kvmmap + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat v0 b with "Hcg Hpc Hi04 [Hc2]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2".
    iEval (rewrite HspW1 Hb2) in "Hc2".
    (* same [rget]-at-the-caller's-hart bridge as [Hc1] above (this leaf was
       applied at CID2). *)
    iEval (rgne) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r8) in "Hc2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.kvmmap + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.kvmmap + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.kvmmap + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (P2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.kvmmap + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.kvmmap + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 mv a5,a3 (a5 := sz) *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmap + 0x08)) (mword_of_int 15 : mword 5) (mword_of_int 13 : mword 5)
              P2 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    (* the leaf's write value is [add_vec zero_reg (rget m rs2)], let-bound
       outside its own [wp_next] -- read at the CALLER's ambient hart (CID4,
       active when this leaf was applied). [rgne] peels it to the CID-free
       [!!!] form so the plain [!!!]-spelled [set] below folds by [change]. *)
    iEval (rgne) in "Hcg".
    set (P3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (P2 !!! Regidx (mword_of_int 13 : mword 5)))]> P2).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.kvmmap + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.kvmmap + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a mv a3,a2 (a3 := pa) *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmap + 0x0a)) (mword_of_int 13 : mword 5) (mword_of_int 12 : mword 5)
              P3 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    (* same bridge as above (this leaf was applied at CID5). *)
    iEval (rgne) in "Hcg".
    set (P4 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (add_vec zero_reg (P3 !!! Regidx (mword_of_int 12 : mword 5)))]> P3).
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.kvmmap + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.kvmmap + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c mv a2,a5 (a2 := sz) *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmap + 0x0c)) (mword_of_int 12 : mword 5) (mword_of_int 15 : mword 5)
              P4 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    (* same bridge as above (this leaf was applied at CID6). *)
    iEval (rgne) in "Hcg".
    set (P5 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (add_vec zero_reg (P4 !!! Regidx (mword_of_int 15 : mword 5)))]> P4).
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.kvmmap + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.kvmmap + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e jal mappages *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kvmmap + 0x0e)) (mword_of_int 1 : mword 5) (mword_of_int 2096956 : mword 21)
              P5 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0e").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (P6 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kvmmap + 0x0e) : mword 64) 4)]> P5).
    assert (Hpcmp : add_vec (mword_of_int (KernelSyms.kvmmap + 0x0e) : mword 64) (sign_extend' 64 (mword_of_int 2096956 : mword 21)) = mword_of_int KernelSyms.mappages) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcmp) in "Hpc".
    (* ---- the swapped-argument facts at mappages entry ---- *)
    assert (HP6sp : P6 !!! Regidx csp_rs1 = spr).
    { rewrite /P6 /P5 /P4 /P3 /P2.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact HspW1. }
    assert (HP6a0 : P6 !!! Regidx (mword_of_int 10 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite /P6 /P5 /P4 /P3 /P2 /W1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact Hroot. }
    assert (HP6a1 : P6 !!! Regidx (mword_of_int 11 : mword 5) = va).
    { rewrite /P6 /P5 /P4 /P3 /P2 /W1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      reflexivity. }
    assert (HP6a2 : P6 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int (Z.of_nat npages * 4096)).
    { rewrite /P6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_eq.
      rewrite add_vec_zero_l.
      rewrite /P4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_eq.
      rewrite add_vec_zero_l.
      rewrite /P2 /W1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact Hsz. }
    assert (HP6a3 : P6 !!! Regidx (mword_of_int 13 : mword 5) = pa).
    { rewrite /P6. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /P5. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_eq.
      rewrite add_vec_zero_l.
      rewrite /P3 /P2 /W1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      reflexivity. }
    assert (HP6a4 : P6 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int perm).
    { rewrite /P6 /P5 /P4 /P3 /P2 /W1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact Hpermreg. }
    (* ---- THE CALL.  [Hcnt : cpu_own lvl eb p C b] was introduced at this
       function's ENTRY hart; the eight plain instructions above were each
       threaded through a FRESH, universally quantified hart (CID1..CID8),
       so the callee wants it at CID8.  [cpu_own_transport] moves it there:
       at [b = true] the hart-indexed payload is not in [cpu_own] at all
       (it rides in [sie_arm]'s enabled arm, re-delivered at CID8 inside
       [Hcg]), and at [b = false] no trap was taken, which is exactly the
       conditional equality Hs1..Hs8 accumulate -- [wp_next_chain] composes
       them.  ONE line, no case split on [b]. ---- *)
    iDestruct (cpu_own_transport CID CID8 lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Mappages.wp_mappages_sconf γa P6 t m npages perm lvl (K - 2)%nat eb p (Some nb) b lks
              Hlvl ltac:(lia)
              HP6a0
              ltac:(rewrite HP6a1; exact Hvaal)
              ltac:(rewrite HP6a3; exact Hpaal)
              HP6a2 Hnp HP6a4 Hpok
              ltac:(rewrite HP6a1; exact Hvab)
              ltac:(rewrite HP6a3; exact Hpab)
              Hrep
              ltac:(rewrite HP6a1; exact Hnone)
              with "Hcg Hcnt Htext Hpc Hptree Henv").
    all: try lkbelow.
    iIntros (CID9 Hs9 mr t' k g)
      "Hcg Hcnt Hpc Hptree %Hnodes Henv %Hkcs %Hbase' %Hrep' %Hpresent %Hmiss %Hpay".
    (* pc back at +0x12; the frame cells recovered *)
    assert (HP6link : P6 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.kvmmap + 0x0e) : mword 64) 4).
    { rewrite /P6 upd_eq. reflexivity. }
    assert (Hret12 : ret_pc (P6 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kvmmap + 0x12)).
    { rewrite HP6link. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret12) in "Hpc".
    (* recovered facts *)
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HP6sp. }
    rewrite HP6a1 in Hrep'. rewrite HP6a3 in Hrep'. rewrite HP6a1 in Hmiss.
    iPoseProof (ki_12 with "Htext") as "Hi12'".
    iPoseProof (ki_14 with "Htext") as "Hi14'".
    iPoseProof (ki_16 with "Htext") as "Hi16'".
    iPoseProof (ki_18 with "Htext") as "Hi18'".
    iPoseProof (ki_1a with "Htext") as "Hi1a'".
    destruct Hpay as [(Hkn & Ha0z) | (Hklt & Ha0m1 & Havz)].
    2:{ (* ---- mappages FAILED (a0 = -1): DEAD.  The counted budget's sharp
           bound [g <= pt_missing t vpn0 npages < nb] refutes the
           [avail_zero] witness (no page was left, yet the counter already
           says zero).  [Hmiss] came back through [Mappages.wp_mappages_sconf]
           already rewritten by [HP6a1] (line above), so it reads [svpn_of va]
           where [Hnbk] still reads the local [vpn0] -- fold it to match. *)
      change vpn0 with (svpn_of va) in Hnbk.
      rewrite avail_sub_Some in Havz. cbn in Havz.
      exfalso. lia. }
    (* ---- mappages SUCCEEDED (k = npages, a0 = 0): bnez FALLS, epilogue ---- *)
    subst k.
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.kvmmap + 0x12)) (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              mr (K - 2)%nat b
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Ha0z; vm_compute; reflexivity)
              with "Hcg Hpc Hi12'").
    iIntros (CIDe Hse) "Hcg Hpc".
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.kvmmap + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.kvmmap + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 ld ra,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kvmmap + 0x14)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              mr (K - 2)%nat (mm !!! Regidx (mword_of_int 1)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14' [Hc1]").
    { iEval (rewrite Hmrsp Hb1). iExact "Hc1". }
    iIntros (CIDf Hsf) "Hcg Hpc Hc1".
    iEval (rewrite Hmrsp Hb1) in "Hc1".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1))]> mr).
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.kvmmap + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.kvmmap + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 ld s0,0(sp) *)
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
    { rewrite /E1. rewrite upd_ne; [| vm_compute; discriminate]. exact Hmrsp. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kvmmap + 0x16)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 2)%nat (mm !!! Regidx (mword_of_int 8)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16' [Hc2]").
    { iEval (rewrite HspE1 Hb2). iExact "Hc2". }
    iIntros (CIDg Hsg) "Hcg Hpc Hc2".
    iEval (rewrite HspE1 Hb2) in "Hc2".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8))]> E1).
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.kvmmap + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.kvmmap + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.addi sp,+16 : move_up 2 *)
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spr).
    { rewrite /E2. rewrite upd_ne; [| vm_compute; discriminate]. exact HspE1. }
    set (E3 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    assert (HspE3 : E3 !!! Regidx csp_rs1 = sp0).
    { rewrite /E3 upd_eq. rewrite HspE2.
      unfold regval_into_reg, spr, sp0. apply frame_cancel_16. }
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite -HspE3. rewrite /E3 upd_eq. reflexivity. }
    assert (Hpop : E2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv HspE2. symmetry. exact Hsprstk. }
    iAssert (stack_own sp0 2) with "[Hc1 Hc2]" as "Hfr".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
      iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
      done. }
    iEval (rewrite -Hwv) in "Hfr".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.kvmmap + 0x18)) (mword_of_int 16 : mword 6)
              E2 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc Hi18' Hfr").
    iIntros (CIDh Hsh) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2) with E3.
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.kvmmap + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.kvmmap + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a ret *)
    assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /E3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /E2. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq. reflexivity. }
    assert (Hrt : ret_pc (E3 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt).
    { rewrite HE3ra. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.kvmmap + 0x1a)) (mword_of_int 1 : mword 5) E3 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1a'").
    iIntros (CIDi Hsi) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite Hrt) in "Hpc".
    (* [cpu_own] again: it was delivered at CID9 by mappages' own [wp_next];
       five more plain instructions have moved the hart to CIDi. *)
    iDestruct (cpu_own_transport CID9 CIDi lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDi with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! E3 t' g with "Hcg Hcnt Hpc Hptree [%] Henv [%] [%] [%] [%] [%]").
    { exact Hnodes. }
    { (* callee_saved mm E3 *)
      pose proof (fun c Hc => callee_saved_lookup Hkcs c Hc) as Hcs.
      unfold callee_saved.
      assert (Hagree : forall c : mword 5, is_cs_idx c = true ->
                c <> mword_of_int 8 -> c <> csp_rs1 ->
                mr !!! Regidx c = mm !!! Regidx c).
      { intros c Hc Hc8 Hcsp.
        rewrite (Hcs c Hc).
        rewrite /P6 /P5 /P4 /P3 /P2 /W1.
        repeat (rewrite upd_ne;
          [| intros Habs; injection Habs as Habs2; subst c;
             first [ apply Hc8; reflexivity | apply Hcsp; reflexivity | vm_compute in Hc; discriminate ] ]).
        reflexivity. }
      split.
      { rewrite HspE3. reflexivity. }
      split.
      { rewrite /E3. rewrite upd_ne; [| vm_compute; discriminate].
        rewrite /E2 upd_eq. reflexivity. }
      all: repeat split;
        (rewrite /E3; rewrite upd_ne; [| vm_compute; discriminate];
         rewrite /E2; rewrite upd_ne; [| vm_compute; discriminate];
         rewrite /E1; rewrite upd_ne; [| vm_compute; discriminate];
         apply Hagree; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]).
    }
    { exact Hbase'. }
    { exact Hrep'. }
    { exact Hpresent. }
    { exact Hmiss. }
  Qed.

End ProofKvmmap.

End KvmmapProof.
