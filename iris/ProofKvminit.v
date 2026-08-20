(* ProofKvminit.v -- whole-function proof of kvminit (kernel/vm.c):
   kvmmake() then store its result into the global [kernel_pagetable] cell.
   Straight-line, one call, no branches; boot-only (COUNTED, STRICT budget),
   so unconditional success.

   Structure: a 2-slot frame push (ra/s0 saves), the kvmmake jal, an
   auipc/sd pair writing the returned root byte address into the identity
   8-byte [kernel_pagetable] cell (@ 0x8000a290), then the frame teardown
   and ret.  The single functor [KvminitProof (KMK : KVMMAKE)] threads
   KMK.wp_kvmmake_sconf's post through verbatim (its budget premise
   [K_kvmmake < nb] forwards unchanged; the callee K = our K - 2). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad list_numbers bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import RegFile WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpLock.
Require Import CalleeSaved StackOwn.
Require Import CodeKvminit.
Require Import SpecKvmmake SpecKvminit.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

(* clean-context (mword-free) nat bounds, so [lia] never sees a bv. *)
Lemma kii_cap_bounds (K : nat) : (50 <= K)%nat -> (2 <= K)%nat /\ (48 <= K - 2)%nat.
Proof. lia. Qed.

Lemma kii_nk (K : nat) : (2 <= K)%nat -> ((K - 2) + 2)%nat = K.
Proof. lia. Qed.

(* ===================================================================== *)
(* THE BODY: sealed and parameterized by the kvmmake WP hypothesis.       *)
(* ===================================================================== *)
Section KvminitBody.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* [CID] is bound HERE, per-hypothesis, rather than reused from the
     Section's own [Context `{GEN : GenId} `{CID : CpuId}] -- this Hypothesis stands in for
     [KMK.wp_kvmmake_sconf] (a Module Type Parameter, hence ALREADY fully
     CID-generic), and the body below must be able to apply it at a hart
     other than the section's own (after several b-generic leaf steps below
     migrate to a fresh CID). Without its own binder, [wp_kvmmake] would be
     fixed at the section's single ambient CID and could never be invoked at
     a migrated one at all -- a strictly more basic obstruction than the
     [cpu_own] gap documented at the call site below. Per the porting guide's
     "KEEP the section's Context... only remove it from a file that must
     apply its OWN lemmas at a migrated hart, and then make CID an implicit
     per-lemma binder" -- exactly this situation. *)
  Hypothesis wp_kvmmake :
    forall `{CID : CpuId} (γa : gname) (mm : regfile) (lvl K : nat)
      (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string),
      wp_kvmmake_sconf_body γa mm lvl K eb p on b lks.

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Lemma wp_kvminit_sconf_gen (γa : gname) (mm : regfile)
      (lvl K : nat) (eb : bool) (p : mword 64) (on : option nat) (kpt0 : mword 64) (b : bool) (lks : gset string) :
    wp_kvminit_sconf_body γa mm lvl K eb p on kpt0 b lks.
  Proof.
    unfold wp_kvminit_sconf_body.
    intros Hlvl HK Hex Hlkbelow.
    destruct Hex as (nb & Hon & Hnbk). subst lvl. subst on.
    pose proof (kii_cap_bounds K HK) as (Hc2 & HKmk).
    iIntros "Hcg Hcnt #Htext Hpc Hcell Henv Hcont".
    (* frame-cell address facts (2-slot frame: ra @ slot 1, s0 @ slot 2) *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : add_vec (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk (mm !!! Regidx csp_rs1) 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk (mm !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (kii_00 with "Htext") as "Hi00".
    iPoseProof (kii_02 with "Htext") as "Hi02".
    iPoseProof (kii_04 with "Htext") as "Hi04".
    iPoseProof (kii_06 with "Htext") as "Hi06".
    iPoseProof (kii_08 with "Htext") as "Hi08".
    iPoseProof (kii_0c with "Htext") as "Hi0c".
    iPoseProof (kii_10 with "Htext") as "Hi10".
    iPoseProof (kii_14 with "Htext") as "Hi14".
    iPoseProof (kii_16 with "Htext") as "Hi16".
    iPoseProof (kii_18 with "Htext") as "Hi18".
    iPoseProof (kii_1a with "Htext") as "Hi1a".
    (* +0x00 addi sp,sp,-16 : 2-slot frame push *)
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int KernelSyms.kvminit) (mword_of_int 48 : mword 6) mm K 2 b Hc2 Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    iEval (rewrite (stack_own_slots (KTR := KT0)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /W1 upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int KernelSyms.kvminit : mword 64) 2 = mword_of_int (KernelSyms.kvminit + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,8(sp) -> slot 1 *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kvminit + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 2)%nat v1 b with "Hcg Hpc Hi02 [Hc1]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1". iEval (rewrite HspW1 Hb1) in "Hc1".
    (* the leaf's [storeval] is [rget m rs2], let-bound outside its own
       [wp_next] -- read at the CALLER's ambient hart (CID1, active when this
       leaf was applied). [rgne] peels it to the CID-free [!!!] form. *)
    iEval (rgne) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r1) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.kvminit + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.kvminit + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,0(sp) -> slot 2 *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kvminit + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat v2 b with "Hcg Hpc Hi04 [Hc2]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2". iEval (rewrite HspW1 Hb2) in "Hc2".
    (* same bridge as above (this leaf was applied at CID2). *)
    iEval (rgne) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)) by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r8) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.kvminit + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.kvminit + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 addi s0,sp,16 (value unused; s0 reloaded at the epilogue) *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.kvminit + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.kvminit + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.kvminit + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 jal kvmmake *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kvminit + 0x08)) (mword_of_int 1 : mword 5) (mword_of_int 2096970 : mword 21)
              W2 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (J := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kvminit + 0x08) : mword 64) 4)]> W2).
    assert (Htgt : add_vec (mword_of_int (KernelSyms.kvminit + 0x08) : mword 64) (sign_extend' 64 (mword_of_int 2096970 : mword 21)) = mword_of_int KernelSyms.kvmmake) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt) in "Hpc".
    assert (HJsp : J !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite /J upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq]. rewrite /W1 upd_eq. reflexivity. }
    (* ---- THE CALL: kvminit's own body has FIVE plain instructions (the
       frame push, two sdsp, the addi4spn, and the jal itself) before this
       call, none of which disables interrupts, so by the b-generic recipe
       each was threaded via a fresh, universally quantified hart
       (CID1..CID5 above). [Hcnt : cpu_own lvl eb p C b] was introduced ONCE
       at this function's entry hart; [cpu_own_transport] (CpuOwn.v) moves it
       to CID5 in one line, no case split on [b] -- exactly ProofKvmmap.v's
       two uses of the same lemma. ---- *)
    iDestruct (cpu_own_transport CID CID5 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (wp_kvmmake γa J 0%nat (K - 2)%nat eb p (Some nb) b lks
              eq_refl HKmk
              ltac:(exists nb; split; [reflexivity | exact Hnbk])
              with "Hcg Hcnt Htext Hpc Henv").
    all: try lkbelow.
    iIntros (CID6 Hs6 mr t pas) "Hcg Hcnt Hpc Hptree %Ha0 %Hrep %Hnodes Henv %Hcs %Hpasok Hpages".
    assert (Hret0c : ret_pc (J !!! Regidx (mword_of_int 1)) = mword_of_int (KernelSyms.kvminit + 0x0c)).
    { rewrite /J upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret0c) in "Hpc".
    (* +0x0c auipc a5,0x9 : a5 := 0x8000a196 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kvminit + 0x0c)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 20)
              mr (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (A0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kvminit + 0x0c) : mword 64) (auipc_off (mword_of_int 9 : mword 20)))]> mr).
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.kvminit + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.kvminit + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* +0x10 sd a0,266(a5) : store root byte address into kernel_pagetable *)
    assert (Haddr : add_vec (A0 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 300 : mword 12)) = mword_of_int KernelSyms.kernel_pagetable).
    { rewrite /A0 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HA0_10 : A0 !!! Regidx (mword_of_int 10 : mword 5) = mr !!! Regidx (mword_of_int 10)) by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    iApply (wp_sd_s_sconf (kt := KT0) (ktd := KT0) (mword_of_int (KernelSyms.kvminit + 0x10)) (mword_of_int 10 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 300 : mword 12)
              A0 (K - 2)%nat kpt0 b with "Hcg Hpc Hi10 [Hcell]").
    { (* the leaf's [pa] is [rget A0 rs1], let-bound outside its own
         [wp_next] -- read at the CALLER's ambient hart (CID7). *)
      iEval (rgne). iEval (rewrite Haddr). iExact "Hcell". }
    iIntros (CID8 Hs8) "Hcg Hpc Hcell".
    (* here both [pa]'s [rget A0 rs1] and [storeval]'s [rget A0 rs2] appear;
       two [rgne]s peel each down to the CID-free [!!!] form before the plain
       map-chain facts rewrite. *)
    iEval (rgne) in "Hcell".
    iEval (rgne) in "Hcell".
    iEval (rewrite Haddr HA0_10 Ha0) in "Hcell".
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.kvminit + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.kvminit + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* ---- callee-saved facts through kvmmake ---- *)
    assert (HA0sp : A0 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite /A0 upd_ne; [| reg_neq]. rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HJsp. }
    (* +0x14 ld ra,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kvminit + 0x14)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              A0 (K - 2)%nat (mm !!! Regidx (mword_of_int 1)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [Hc1]").
    { iEval (rewrite HA0sp Hb1). iExact "Hc1". }
    iIntros (CID9 Hs9) "Hcg Hpc Hc1". iEval (rewrite HA0sp Hb1) in "Hc1".
    set (L1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1))]> A0).
    assert (HL1sp : L1 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /L1 upd_ne; [| reg_neq]; exact HA0sp).
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.kvminit + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.kvminit + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* +0x16 ld s0,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kvminit + 0x16)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              L1 (K - 2)%nat (mm !!! Regidx (mword_of_int 8)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [Hc2]").
    { iEval (rewrite HL1sp Hb2). iExact "Hc2". }
    iIntros (CID10 Hs10) "Hcg Hpc Hc2". iEval (rewrite HL1sp Hb2) in "Hc2".
    set (L2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8))]> L1).
    assert (HL2sp : L2 !!! Regidx csp_rs1 = add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) by (rewrite /L2 upd_ne; [| reg_neq]; exact HL1sp).
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.kvminit + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.kvminit + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    (* +0x18 addi sp,sp,16 : the frame pop *)
    assert (Hwv : add_vec (L2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = mm !!! Regidx csp_rs1).
    { rewrite HL2sp. apply frame_cancel_16. }
    assert (Hpop : L2 !!! Regidx csp_rs1 = pa_stk (add_vec (L2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv. rewrite HL2sp. exact Hpush. }
    iAssert (stack_own (KTR := KT0) (mm !!! Regidx csp_rs1) 2) with "[Hc1 Hc2]" as "Hframe".
    { rewrite (stack_own_slots (KTR := KT0)); cbn [seq].
      iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
      iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.kvminit + 0x18)) (mword_of_int 16 : mword 6)
              L2 (K - 2)%nat 2 b Hpop with "Hcg Hpc Hi18 Hframe").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (Efin := <[Regidx csp_rs1 := regval_into_reg (add_vec (L2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> L2).
    iEval (rewrite (kii_nk K Hc2)) in "Hcg".
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.kvminit + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.kvminit + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    (* +0x1a ret *)
    assert (HEfin1 : Efin !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /Efin upd_ne; [| reg_neq]. rewrite /L2 upd_ne; [| reg_neq]. rewrite /L1 upd_eq. reflexivity. }
    assert (Hrt : ret_pc (Efin !!! Regidx (mword_of_int 1 : mword 5)) = ret_pc (mm !!! Regidx (mword_of_int 1))) by (rewrite HEfin1; reflexivity).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.kvminit + 0x1a)) (mword_of_int 1 : mword 5) Efin K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi1a").
    iIntros (CID12 Hs12) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite Hrt) in "Hpc".
    (* [cpu_own] again: it was delivered at CID6 by kvmmake's own [wp_next];
       six more plain instructions (auipc, sd, two cldsp, the sp pop, ret)
       have moved the hart to CID12. *)
    iDestruct (cpu_own_transport CID6 CID12 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CID12 with "[]"); [ iPureIntro; wp_next_chain | ].
    (* ---- hand the continuation kvmmake's post + the updated cell ---- *)
    iApply ("Hcont" $! Efin t pas with "Hcg Hcnt Hpc Hptree Hcell [%] [%] Henv [%] [%] Hpages").
    { exact Hrep. }
    { exact Hnodes. }
    { (* callee_saved mm Efin *)
      unfold callee_saved.
      repeat split;
        first [ by (rewrite /Efin upd_eq; exact Hwv)
              | by (rewrite /Efin upd_ne; [| reg_neq]; rewrite /L2 upd_eq)
              | (rewrite /Efin /L2 /L1 /A0; repeat (rewrite upd_ne; [| reg_neq]);
                 rewrite (callee_saved_lookup Hcs);
                   [ rewrite /J /W2 /W1; repeat (rewrite upd_ne; [| reg_neq]); reflexivity
                   | vm_compute; reflexivity ]) ]. }
    { exact Hpasok. }
  Qed.

End KvminitBody.

(* ===================================================================== *)
(* THE SEALED FUNCTOR: instantiate the kvmmake WP hypothesis with its      *)
(* proven spec, discharging the KVMINIT Module Type.                       *)
(* ===================================================================== *)
Module KvminitProof (KMK : KVMMAKE) : KVMINIT.
  Definition wp_kvminit_sconf `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (mm : regfile) (lvl K : nat) (eb : bool) (p : mword 64) (on : option nat) (kpt0 : mword 64) (b : bool) (lks : gset string)
      : wp_kvminit_sconf_body γa mm lvl K eb p on kpt0 b lks :=
    (* eta-expand the module argument: passed bare, implicit-argument
       insertion would silently resolve [KMK.wp_kvmmake_sconf]'s [CID] at
       THIS definition's own ambient hart, defeating [wp_kvminit_sconf_gen]'s
       hypothesis (which needs it callable at ANY hart). *)
    wp_kvminit_sconf_gen (fun (CID' : CpuId) => KMK.wp_kvmmake_sconf (CID:=CID')) γa mm lvl K eb p on kpt0 b lks.
End KvminitProof.
