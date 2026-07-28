(* ProofUvmcreate.v -- whole-function proof of uvmcreate (kernel/vm.c):
   a 4-slot frame, one kalloc, the null test, memset(p,0,4096), and the
   epilogue.  Straight-line under the counted budget: the null arm is dead.

   The body is the same shape as kvmmake's prologue (ProofKvmmake's
   [wp_kmk_prologue_node]) -- kalloc + memset + [zero_page_to_node] -- with
   the frame pop and the [beqz] fall-through added, since here it IS the
   whole function. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad list_numbers bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore RegFile WpMmodeLeafBase.
Require Import IntrDefs WpSmodeIntr WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpLock.
Require Import CalleeSaved StackOwn.
Require Import ProcGeom.
Require Import KallocInv.
Require Import KMap.            (* mem_page_to_phys *)
Require Import PtTree PtBuild KptPt KptTree KvmSpec.
Require Import WpMemsetPage.    (* bytes_choose *)
Require Import WpUvmcreateInstr.
Require Import SpecKalloc SpecMemset SpecUvmcreate.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* clean-context (mword-free) stack-slot arithmetic, so [lia] never sees a bv *)
Lemma uvc_cap_bounds (K : nat) : (18 <= K)%nat ->
  (4 <= K)%nat /\ (2 <= K - 4)%nat /\ (14 <= K - 4)%nat.
Proof. lia. Qed.

(* Z-only (bv-free) node-page range arithmetic, so [lia] never sees a bv --
   the heavy-import context breaks lia's zify hook otherwise. *)
Lemma uvc_kdata_bound_arith (z : Z) :
  (z mod 4096 = 0)%Z -> (0x80023558 <= z)%Z -> (z < 0x88000000)%Z ->
  (ram_base <= z)%Z /\ (z + 4096 <= ram_base + ram_size)%Z.
Proof.
  intros Hm Hlo Hhi. apply Z.mod_divide in Hm; [| lia]. destruct Hm as [k Hk].
  unfold ram_base, ram_size. lia.
Qed.

Lemma uvc_kda_arith (z : Z) : (0x80023558 <= z)%Z -> (text_end <= z)%Z.
Proof. unfold text_end. lia. Qed.

Lemma uvc_sp_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64) = 18446744073709551584) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64) = 32) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551584 + 32) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

Module UvmcreateProof (AK : KALLOC) (MS : MEMSET) : UVMCREATE.

Section ProofUvmcreate.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  Notation UVC := KernelSyms.uvmcreate.

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.
  Ltac peel_reg_step :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].
  Ltac peel_reg := peel_reg_step; reflexivity.

  Lemma wp_uvmcreate_sconf (γ : gname) (γa : gname) (Φ : mval -> iProp Σ)
      (mm : regfile) (lvl K : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (on : option nat)
    : wp_uvmcreate_sconf_body γ γa Φ mm lvl K eb p C on.
  Proof.
    cbv beta delta [wp_uvmcreate_sconf_body].
    intros ret_tgt Hlvl HK Hex Hcid.
    destruct Hex as (nb & Hon & Hnb). subst lvl. subst on.
    pose proof (uvc_cap_bounds K HK) as (Hc4 & Hc2 & Hc14).
    set (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hcnt #Htext Hpc Henv Hcont".
    (* frame-cell address facts *)
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 4 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (uvci_00 with "Htext") as "Hi00".
    iPoseProof (uvci_02 with "Htext") as "Hi02".
    iPoseProof (uvci_04 with "Htext") as "Hi04".
    iPoseProof (uvci_06 with "Htext") as "Hi06".
    iPoseProof (uvci_08 with "Htext") as "Hi08".
    iPoseProof (uvci_0a with "Htext") as "Hi0a".
    iPoseProof (uvci_0e with "Htext") as "Hi0e".
    iPoseProof (uvci_10 with "Htext") as "Hi10".
    iPoseProof (uvci_12 with "Htext") as "Hi12".
    iPoseProof (uvci_14 with "Htext") as "Hi14".
    iPoseProof (uvci_16 with "Htext") as "Hi16".
    iPoseProof (uvci_1a with "Htext") as "Hi1a".
    iPoseProof (uvci_1c with "Htext") as "Hi1c".
    iPoseProof (uvci_1e with "Htext") as "Hi1e".
    iPoseProof (uvci_20 with "Htext") as "Hi20".
    iPoseProof (uvci_22 with "Htext") as "Hi22".
    iPoseProof (uvci_24 with "Htext") as "Hi24".
    (* +0x00 addi sp,sp,-32 *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf γ Φ (mword_of_int UVC) (mword_of_int 32 : mword 6) mm K 4 Hc4 Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    iDestruct "S3" as (v3) "Hc3". iDestruct "S4" as (v4) "Hc4".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr) by (rewrite /W1; rewrite upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int UVC : mword 64) 2 = mword_of_int (UVC + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,24(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (UVC + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 4)%nat v1 with "Hcg Hpc Hi02 [Hc1] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros "Hcg Hpc Hc1". iEval (rewrite HspW1 Hb1) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r1) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (UVC + 0x02) : mword 64) 2 = mword_of_int (UVC + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,16(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (UVC + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 4)%nat v2 with "Hcg Hpc Hi04 [Hc2] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros "Hcg Hpc Hc2". iEval (rewrite HspW1 Hb2) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r8) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (UVC + 0x04) : mword 64) 2 = mword_of_int (UVC + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 sd s1,8(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (UVC + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              W1 (K - 4)%nat v3 with "Hcg Hpc Hi06 [Hc3] [-]").
    { iEval (rewrite HspW1 Hb3). iExact "Hc3". }
    iIntros "Hcg Hpc Hc3". iEval (rewrite HspW1 Hb3) in "Hc3".
    assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r9) in "Hc3".
    assert (Hp08 : add_vec_int (mword_of_int (UVC + 0x06) : mword 64) 2 = mword_of_int (UVC + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 addi s0,sp,32 (value unused; s0 reloaded at the epilogue) *)
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (UVC + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 4)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi08 [-]").
    iIntros "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> W1).
    assert (Hp0a : add_vec_int (mword_of_int (UVC + 0x08) : mword 64) 2 = mword_of_int (UVC + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a jal kalloc *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (UVC + 0x0a)) (mword_of_int 1 : mword 5) (mword_of_int 2095436 : mword 21)
              W2 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a [-]").
    iIntros "Hcg Hpc".
    set (J := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (UVC + 0x0a) : mword 64) 4)]> W2).
    assert (Htgtk : add_vec (mword_of_int (UVC + 0x0a) : mword 64) (sign_extend' 64 (mword_of_int 2095436 : mword 21)) = mword_of_int KernelSyms.kalloc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtk) in "Hpc".
    iDestruct "Henv" as (γk) "(#Hlock & Havail & #Hpanic)".
    assert (HJ4 : J !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite /J /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HJsp : J !!! Regidx csp_rs1 = spr).
    { rewrite /J /W2. repeat (rewrite upd_ne; [| reg_neq]). exact HspW1. }
    assert (HcidJ : J !!! Regidx (mword_of_int 4 : mword 5) = cid_word)
      by (rewrite HJ4; exact Hcid).
    iApply (AK.wp_kalloc_sconf γ Φ γa γk (mword_of_int (KernelSyms.kmem + 24))
              J (Some nb) 0%nat eb p C (K - 4)%nat
              Hc14
              HcidJ
              ltac:(reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hcnt Htext Hpc Hlock Havail Hpanic [-]").
    iIntros (mr0) "Hcg Hcnt Hpc %Hkcs0 Hkpost".
    assert (Hret0e : ret_pc (J !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (UVC + 0x0e)).
    { rewrite /J upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret0e) in "Hpc".
    (* success arm: nb > 0, so kalloc cannot fail *)
    assert (Hcnt : Some nb = Some (S (nb - 1))) by (f_equal; lia).
    iEval (rewrite Hcnt) in "Hkpost".
    iDestruct (kalloc_post_success with "Hkpost") as "(%Hpv & Hpage & Havail2)".
    assert (Hav1 : Some (nb - 1)%nat = avail_sub (Some nb) 1) by (rewrite avail_sub_Some; reflexivity).
    iEval (rewrite Hav1) in "Havail2".
    iAssert (kalloc_env γa (avail_sub (Some nb) 1) (mm !!! Regidx (mword_of_int 4)))
      with "[Havail2]" as "Henv".
    { iExists γk. iFrame "Hlock Havail2 Hpanic". }
    set (root0 := mr0 !!! Regidx (mword_of_int 10 : mword 5)).
    assert (Hmr0sp : mr0 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs0 csp_rs1 ltac:(vm_compute; reflexivity)). exact HJsp. }
    assert (Hmr0tp : mr0 !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite (callee_saved_lookup Hkcs0 (mword_of_int 4) ltac:(vm_compute; reflexivity)). exact HJ4. }
    (* +0x0e mv s1,a0 *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (UVC + 0x0e)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mr0 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0e [-]").
    iIntros "Hcg Hpc".
    set (M1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (mr0 !!! Regidx (mword_of_int 10 : mword 5)))]> mr0).
    assert (Hp10 : add_vec_int (mword_of_int (UVC + 0x0e) : mword 64) 2 = mword_of_int (UVC + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* +0x10 beqz a0 -- FALLS: a kalloc'd page is never null *)
    assert (HM1a0 : M1 !!! Regidx (mword_of_int 10 : mword 5) = root0)
      by (rewrite /M1; rewrite upd_ne; [reflexivity | reg_neq]).
    assert (Hnz : (zero_reg : mword 64) = nullp) by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (UVC + 0x10)) (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              M1 (K - 4)%nat
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite HM1a0; apply eq_vec_false_iff; rewrite Hnz;
                    exact (page_valid_ne_null _ Hpv))
              with "Hcg Hpc Hi10 [-]").
    iIntros "Hcg Hpc".
    assert (Hp12 : add_vec_int (mword_of_int (UVC + 0x10) : mword 64) 2 = mword_of_int (UVC + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    (* +0x12 lui a2,0x1 *)
    iApply (wp_clui_s_sconf γ Φ (mword_of_int (UVC + 0x12)) (mword_of_int 12 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6)) (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))
              M1 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(reflexivity) with "Hcg Hpc Hi12 [-]").
    iIntros "Hcg Hpc".
    set (M2 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> M1).
    assert (Hp14 : add_vec_int (mword_of_int (UVC + 0x12) : mword 64) 2 = mword_of_int (UVC + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* +0x14 li a1,0 *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (UVC + 0x14)) (mword_of_int 11 : mword 5) (mword_of_int 0 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
              M2 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(reflexivity) with "Hcg Hpc Hi14 [-]").
    iIntros "Hcg Hpc".
    set (M3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> M2).
    assert (Hp16 : add_vec_int (mword_of_int (UVC + 0x14) : mword 64) 2 = mword_of_int (UVC + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* +0x16 jal memset *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (UVC + 0x16)) (mword_of_int 1 : mword 5) (mword_of_int 2095834 : mword 21)
              M3 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi16 [-]").
    iIntros "Hcg Hpc".
    set (M4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (UVC + 0x16) : mword 64) 4)]> M3).
    assert (Htgtm : add_vec (mword_of_int (UVC + 0x16) : mword 64) (sign_extend' 64 (mword_of_int 2095834 : mword 21)) = mword_of_int KernelSyms.memset) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtm) in "Hpc".
    (* memset(root, 0, 4096): bridge page_own to the per-byte buffer *)
    assert (HM4a0 : M4 !!! Regidx (mword_of_int 10 : mword 5) = root0).
    { rewrite /M4 /M3 /M2 /M1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HM4a1 : M4 !!! Regidx (mword_of_int 11 : mword 5) = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))).
    { rewrite /M4. rewrite upd_ne; [| reg_neq]. rewrite /M3 upd_eq. reflexivity. }
    assert (HM4a2 : M4 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int (Z.of_nat 4096)).
    { rewrite /M4 /M3. repeat (rewrite upd_ne; [| reg_neq]). rewrite /M2 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite /page_own /byte_any) in "Hpage".
    iDestruct (bytes_choose 4096 0 (fun j b => ((pa_add root0 j) ↦ₘ b)%I) with "Hpage") as (olds) "Hbuf".
    iApply (MS.wp_memset_sconf γ Φ M4 (K - 4)%nat 4096 (M4 !!! Regidx (mword_of_int 11 : mword 5)) olds
              Hc2 ltac:(vm_compute; reflexivity) ltac:(reflexivity) HM4a2
              with "Hcg Htext Hpc [Hbuf] [-]").
    { iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H". rewrite HM4a0. iExact "H". }
    iIntros (mfin) "Hcg Hpc Hbytes %Hmcs".
    assert (Hret1a : ret_pc (M4 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (UVC + 0x1a)).
    { rewrite /M4 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret1a) in "Hpc".
    (* the written buffer is all-zero bytes *)
    assert (Hcb : nth_byte (autocast (T := mword) (subrange_vec_dec (M4 !!! Regidx (mword_of_int 11 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 = (mword_of_int 0 : mword 8)).
    { rewrite HM4a1. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hcb HM4a0) in "Hbytes".
    (* page geometry: alignment + range *)
    pose proof Hpv as Hpv'. destruct Hpv' as [Hpal [Hplo Hphi]].
    unfold page_aligned, PGSIZE in Hpal. unfold page_in_range, kmem_lo, kmem_hi in Hplo, Hphi.
    rewrite uint_unsigned in Hpal, Hplo, Hphi.
    set (bppn := autocast (T := mword) (subrange_vec_dec root0 55 12) : mword 44).
    assert (Hpbase : zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12)) = root0).
    { unfold bppn. apply walk_alloc_page_base.
      - rewrite uint_unsigned. exact Hpal.
      - rewrite uint_unsigned. apply (Z.lt_trans _ 0x88000000); [exact Hphi | apply Z.ltb_lt; vm_compute; reflexivity]. }
    (* physical-tier bytes + node claim from the static kdata claims *)
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
    iDestruct "Hhwc" as (hwmisa0 hwmseccfg0 hwpmar0 hwelp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb)".
    iDestruct (mem_page_to_phys root0 (DfracOwn 1) (mword_of_int 0 : mword 8)
                 ltac:(intros j Hj; apply kdata_svpn_class; apply page_in_range_addr_is_kdata; [exact Hpv | exact Hj])
                 with "Hkmapb Hbytes") as "Hbytes".
    iEval (rewrite -Hpbase) in "Hbytes".
    assert (Hbppn4k : bv_unsigned bppn * 4096 = bv_unsigned root0).
    { rewrite <- (page_base_unsigned bppn). rewrite Hpbase. reflexivity. }
    assert (Hnkd : node_kdata bppn).
    { unfold node_kdata. rewrite Hbppn4k.
      exact (uvc_kdata_bound_arith (bv_unsigned root0) Hpal Hplo Hphi). }
    assert (Hkda : (text_end <= bv_unsigned bppn * 4096)%Z).
    { rewrite Hbppn4k. exact (uvc_kda_arith (bv_unsigned root0) Hplo). }
    iDestruct (pt_node_claim_from_static bppn Hnkd Hkda with "Hkmapb") as "#Hbclaim".
    iDestruct (zero_page_to_node 2 (DfracOwn 1) bppn with "Hbclaim Hbytes") as "Hptree".
    (* register facts through memset *)
    assert (Hfsp : mfin !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hmcs csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /M4 /M3 /M2 /M1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr0sp. }
    assert (Hfs1 : mfin !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))).
    { rewrite (callee_saved_lookup Hmcs (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /M4 /M3 /M2. repeat (rewrite upd_ne; [| reg_neq]). rewrite /M1 upd_eq.
      rewrite add_vec_zero_l. rewrite Hpbase. reflexivity. }
    (* ---------------- epilogue ---------------- *)
    (* +0x1a mv a0,s1 *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (UVC + 0x1a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              mfin (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1a [-]").
    iIntros "Hcg Hpc".
    set (E0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfin !!! Regidx (mword_of_int 9 : mword 5)))]> mfin).
    assert (Hp1c : add_vec_int (mword_of_int (UVC + 0x1a) : mword 64) 2 = mword_of_int (UVC + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    assert (HE0sp : E0 !!! Regidx csp_rs1 = spr) by (rewrite /E0; rewrite upd_ne; [| reg_neq]; exact Hfsp).
    (* +0x1c ld ra,24(sp) *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (UVC + 0x1c)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              E0 (K - 4)%nat (mm !!! Regidx (mword_of_int 1 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1c [Hc1] [-]").
    { iEval (rewrite HE0sp Hb1). iExact "Hc1". }
    iIntros "Hcg Hpc Hc1". iEval (rewrite HE0sp Hb1) in "Hc1".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> E0).
    assert (Hp1e : add_vec_int (mword_of_int (UVC + 0x1c) : mword 64) 2 = mword_of_int (UVC + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1; rewrite upd_ne; [| reg_neq]; exact HE0sp).
    (* +0x1e ld s0,16(sp) *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (UVC + 0x1e)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 4)%nat (mm !!! Regidx (mword_of_int 8 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1e [Hc2] [-]").
    { iEval (rewrite HE1sp Hb2). iExact "Hc2". }
    iIntros "Hcg Hpc Hc2". iEval (rewrite HE1sp Hb2) in "Hc2".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (Hp20 : add_vec_int (mword_of_int (UVC + 0x1e) : mword 64) 2 = mword_of_int (UVC + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2; rewrite upd_ne; [| reg_neq]; exact HE1sp).
    (* +0x20 ld s1,8(sp) *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (UVC + 0x20)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 4)%nat (mm !!! Regidx (mword_of_int 9 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi20 [Hc3] [-]").
    { iEval (rewrite HE2sp Hb3). iExact "Hc3". }
    iIntros "Hcg Hpc Hc3". iEval (rewrite HE2sp Hb3) in "Hc3".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (Hp22 : add_vec_int (mword_of_int (UVC + 0x20) : mword 64) 2 = mword_of_int (UVC + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spr) by (rewrite /E3; rewrite upd_ne; [| reg_neq]; exact HE2sp).
    (* +0x22 addi sp,sp,32 -- the frame pop *)
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HE3sp. unfold spr. apply uvc_sp_cancel. }
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HE3sp. symmetry. exact Hsprstk. }
    iAssert (stack_own sp0 4) with "[Hc1 Hc2 Hc3 Hc4]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
      iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
      iSplitL "Hc3". { iExists (mm !!! Regidx (mword_of_int 9)). iExact "Hc3". }
      iSplitL "Hc4". { iExists v4. iExact "Hc4". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (UVC + 0x22)) (mword_of_int 2 : mword 6)
              E3 (K - 4)%nat 4 Hpop with "Hcg Hpc Hi22 Hframe [-]").
    iIntros "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hp24 : add_vec_int (mword_of_int (UVC + 0x22) : mword 64) 2 = mword_of_int (UVC + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* +0x24 ret *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by peel_reg.
    assert (Hrt : ret_pc (E4 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt) by (rewrite HE4ra; reflexivity).
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (UVC + 0x24)) (mword_of_int 1 : mword 5) E4 K
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi24 [-]").
    iIntros "Hcg Hpc". iEval (rewrite Hrt) in "Hpc".
    assert (HE4a0 : E4 !!! Regidx (mword_of_int 10 : mword 5)
                    = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))).
    { rewrite /E4. rewrite upd_ne; [| reg_neq]. rewrite /E3. rewrite upd_ne; [| reg_neq].
      rewrite /E2. rewrite upd_ne; [| reg_neq]. rewrite /E1. rewrite upd_ne; [| reg_neq].
      rewrite /E0 upd_eq. rewrite add_vec_zero_l. exact Hfs1. }
    iApply ("Hcont" $! E4 bppn with "Hcg Hcnt Hpc Hptree [%] [%] Henv [%]").
    { exact HE4a0. }
    { rewrite HE4a0 Hpbase. exact Hpv. }
    { (* callee_saved mm E4 *)
      unfold callee_saved.
      split. { rewrite /E4 upd_eq. rewrite HE3sp. unfold spr. apply uvc_sp_cancel. }
      split. { rewrite /E4 /E3 /E2 /E1 /E0. repeat (rewrite upd_ne; [| reg_neq]).
               rewrite (callee_saved_lookup Hmcs (mword_of_int 4) ltac:(vm_compute; reflexivity)).
               rewrite /M4 /M3 /M2 /M1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr0tp. }
      split. { rewrite /E4. rewrite upd_ne; [| reg_neq]. rewrite /E3. rewrite upd_ne; [| reg_neq]. rewrite /E2 upd_eq. reflexivity. }
      split. { rewrite /E4. rewrite upd_ne; [| reg_neq]. rewrite /E3 upd_eq. reflexivity. }
      repeat split;
        (rewrite /E4 /E3 /E2 /E1 /E0; repeat (rewrite upd_ne; [| reg_neq]);
         match goal with
         | |- _ !!! Regidx (mword_of_int ?k) = _ =>
           rewrite (callee_saved_lookup Hmcs (mword_of_int k) ltac:(vm_compute; reflexivity));
           rewrite /M4 /M3 /M2 /M1; repeat (rewrite upd_ne; [| reg_neq]);
           rewrite (callee_saved_lookup Hkcs0 (mword_of_int k) ltac:(vm_compute; reflexivity));
           rewrite /J /W2 /W1; repeat (rewrite upd_ne; [| reg_neq]); reflexivity
         end). }
  Qed.

End ProofUvmcreate.

End UvmcreateProof.
