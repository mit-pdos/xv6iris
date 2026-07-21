(* WpSconfKinit.v -- the whole-function WP for xv6's kinit() over the
   SIE-agnostic sconf world.  kinit() = initlock(&kmem.lock, "kmem") then
   freerange(end, PHYSTOP), with the allocator invariant [is_kmem] and the boot
   page-count token [kalloc_avail γk (Some 0)] freshly allocated in between (the
   "newlock" ghost step).  Straight-line (no loop): a 16-byte frame, two jal
   sub-calls, and the ghost allocation.  Post hands back the freshly minted
   [is_kmem γl γk lk fl] and [kalloc_avail γk (Some (length ps))] -- the count of
   pages freerange just freed. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import WpGpr InstrBytes WpMmodeLeafBase WpAuipc.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn CalleeSaved.
Require Import KernelText.
Require Import WpMycpu WpLock.
Require Import KallocInv.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpInitlock SpecInitlock SpecFreerange.
Require Import WpKinitDecode.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecKinit.
Local Open Scope Z_scope.
Import Defs.

Module KinitProof (Freerange : FREERANGE) (Initlock : INITLOCK) : KINIT.

Section WpSconfKinit.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  Notation KI := KernelSyms.kinit.

  Lemma wp_kinit_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m : regfile)
      (ps : list (mword 64)) (K ncnt : nat)
      (vlock : bv 32) (vname vcpu : bv 64)
    : wp_kinit_sconf_body γ root_ppn Φ m ps K ncnt vlock vname vcpu.
  Proof.
    cbv beta delta [wp_kinit_sconf_body].
    intros pcE sp0 ret_tgt cpuv a_noff a_int lk fl c_name c_cpu endaddr phystop s1entry
      HK Hncnt Hmycpu Hretm Hprun Hnoffdat Hintdat.
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    iIntros "Hsc Hhs Hcg Hcnt Htlbinv #Htext Hpc Hlock Hname Hcpu Hflw Hpages Hqnoff Hqint Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfileki]".
    iDestruct (sie_cap_sid with "Hcap") as "[%Hsidcap Hcap]".
    iDestruct (sie_cap_gpr_join with "Hcap Hfileki") as "Hcg".
    assert (Hsid4 : stack_in_data sp0 4)
      by (apply (stack_in_data_mono _ (kv_frame_slots + K)); [unfold kv_frame_slots; lia | exact Hsidcap]).
    assert (Hspr2 : spr = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hdeepaddr : pa_stk (pa_stk sp0 kv_frame_slots) 2 = pa_stk spr kv_frame_slots).
    { rewrite Hspr2 !pa_stk_assoc. f_equal; lia. }
    iPoseProof (kii_00 with "Htext") as "Hi00".
    iPoseProof (kii_02 with "Htext") as "Hi02".
    iPoseProof (kii_04 with "Htext") as "Hi04".
    iPoseProof (kii_06 with "Htext") as "Hi06".
    iPoseProof (kii_08 with "Htext") as "Hi08".
    iPoseProof (kii_0c with "Htext") as "Hi0c".
    iPoseProof (kii_10 with "Htext") as "Hi10".
    iPoseProof (kii_14 with "Htext") as "Hi14".
    iPoseProof (kii_18 with "Htext") as "Hi18".
    iPoseProof (kii_1c with "Htext") as "Hi1c".
    iPoseProof (kii_1e with "Htext") as "Hi1e".
    iPoseProof (kii_20 with "Htext") as "Hi20".
    iPoseProof (kii_24 with "Htext") as "Hi24".
    iPoseProof (kii_28 with "Htext") as "Hi28".
    iPoseProof (kii_2c with "Htext") as "Hi2c".
    iPoseProof (kii_2e with "Htext") as "Hi2e".
    iPoseProof (kii_30 with "Htext") as "Hi30".
    iPoseProof (kii_32 with "Htext") as "Hi32".
    (* ===== PROLOGUE: 2-slot frame trade (move_down 2) + save ra/s0 ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ pcE (mword_of_int 48 : mword 6) m K 2 ltac:(lia) Hpush
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (vra0) "Hras". iDestruct "S2" as (vs00) "Hs0s".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KI + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,8(sp) *)
    assert (Hd1 : addr_in_data (add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))))
      by (rewrite HspR1 Hb1; apply Hsid4; lia).
    assert (Hd2 : addr_in_data (add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))))
      by (rewrite HspR1 Hb2; apply Hsid4; lia).
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 2)%nat vra0 Hd1 with "Hsc Hhs Hcg Htlbinv Hpc Hi02 [Hras] [-]").
    { iEval (rewrite HspR1 Hb1). iExact "Hras". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hras".
    iEval (rewrite HspR1 Hb1) in "Hras".
    assert (Hrav : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hrav) in "Hras".
    assert (Hpp04 : add_vec_int (mword_of_int (KI + 0x02) : mword 64) 2 = mword_of_int (KI + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat vs00 Hd2 with "Hsc Hhs Hcg Htlbinv Hpc Hi04 [Hs0s] [-]").
    { iEval (rewrite HspR1 Hb2). iExact "Hs0s". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hs0s".
    iEval (rewrite HspR1 Hb2) in "Hs0s".
    assert (Hs0v : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hs0v) in "Hs0s".
    assert (Hpp06 : add_vec_int (mword_of_int (KI + 0x04) : mword 64) 2 = mword_of_int (KI + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi06 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    assert (Hpp08 : add_vec_int (mword_of_int (KI + 0x06) : mword 64) 2 = mword_of_int (KI + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== compute a1 = &"kmem", a0 = &kmem (0x08..0x14) ===== *)
    (* +0x08 auipc a1,0x6 *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x08)) (mword_of_int 11 : mword 5) (mword_of_int 6 : mword 20)
              R2 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi08 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (KI + 0x08) : mword 64) (auipc_off (mword_of_int 6 : mword 20)))]> R2).
    assert (Hpp0c : add_vec_int (mword_of_int (KI + 0x08) : mword 64) 4 = mword_of_int (KI + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c addi a1,a1,1342 *)
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x0c)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 1342 : mword 12)
              R3 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 1342 : mword 12)))]> R3).
    assert (Hpp10 : add_vec_int (mword_of_int (KI + 0x0c) : mword 64) 4 = mword_of_int (KI + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 auipc a0,0x12 *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x10)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 20)
              R4 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi10 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (KI + 0x10) : mword 64) (auipc_off (mword_of_int 18 : mword 20)))]> R4).
    assert (Hpp14 : add_vec_int (mword_of_int (KI + 0x10) : mword 64) 4 = mword_of_int (KI + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 addi a0,a0,-2018  (a0 := &kmem = lk) *)
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x14)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 2078 : mword 12)
              R5 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi14 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2078 : mword 12)))]> R5).
    assert (Hpp18 : add_vec_int (mword_of_int (KI + 0x14) : mword 64) 4 = mword_of_int (KI + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    assert (HR6a0 : R6 !!! Regidx (mword_of_int 10 : mword 5) = lk).
    { rewrite /R6 upd_eq. rewrite /R5 upd_eq.
      unfold lk. apply bv_eq; vm_compute; reflexivity. }
    assert (HR6sp : R6 !!! Regidx csp_rs1 = spr).
    { rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate]. exact HspR1. }
    assert (HR6tp : R6 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    (* ===== jal initlock ===== *)
    (* +0x18 jal ra,initlock *)
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x18)) (mword_of_int 1 : mword 5) (mword_of_int 118 : mword 21)
              R6 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi18 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KI + 0x18) : mword 64) 4)]> R6).
    assert (Htgtil : add_vec (mword_of_int (KI + 0x18) : mword 64) (sign_extend' 64 (mword_of_int 118 : mword 21)) = mword_of_int KernelSyms.initlock) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtil) in "Hpc".
    assert (HR7a0 : R7 !!! Regidx (mword_of_int 10 : mword 5) = lk)
      by (rewrite /R7 upd_ne; [exact HR6a0 | vm_compute; discriminate]).
    assert (HR7sp : R7 !!! Regidx csp_rs1 = spr)
      by (rewrite /R7 upd_ne; [exact HR6sp | vm_compute; discriminate]).
    assert (HR7ra : R7 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KI + 0x18) : mword 64) 4)
      by (rewrite /R7; apply upd_eq).
    assert (HR7tp : R7 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5))
      by (rewrite /R7 upd_ne; [exact HR6tp | vm_compute; discriminate]).
    (* initlock(&kmem.lock, "kmem") : owns lk's 3 struct fields, returns them init'd *)
    assert (Hilstk : stack_in_data (R7 !!! Regidx csp_rs1) 2).
    { rewrite HR7sp Hspr2. apply (stack_in_data_shift sp0 2 2).
      replace (2 + 2)%nat with 4%nat by lia. exact Hsid4. }
    iApply (Initlock.wp_initlock_sconf γ root_ppn Φ R7 vlock vname vcpu (K - 2)
              ltac:(lia)
              ltac:(rewrite HR7ra; vm_compute; reflexivity)
              Hilstk
              ltac:(rewrite HR7a0; unfold addr_in_data; split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity)
              ltac:(rewrite HR7a0; unfold addr_in_data; split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity)
              ltac:(rewrite HR7a0; unfold addr_in_data; split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Htext Hpc [Hlock] [Hname] [Hcpu]").
    { iEval (rewrite HR7a0). iExact "Hlock". }
    { iEval (rewrite HR7a0). iExact "Hname". }
    { iEval (rewrite HR7a0). iExact "Hcpu". }
    iIntros (mil) "Hsc Hhs Hcg Htlbinv Hpc %Hilcs Hlock Hname Hcpu".
    iEval (rewrite HR7a0) in "Hlock". iEval (rewrite HR7a0) in "Hname". iEval (rewrite HR7a0) in "Hcpu".
    assert (Hpcil : update_vec_dec (add_vec (R7 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (KI + 0x1c)).
    { rewrite HR7ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcil) in "Hpc".
    (* ===== newlock ghost: allocate is_kmem γl γk lk fl + kalloc_avail (Some 0) ===== *)
    iApply fupd_wp.
    iMod (own_alloc (Excl () : exclR unitO)) as (γl) "Hlocked"; [done|].
    iMod (kalloc_avail_alloc 0%nat) as (γk) "[Havail Hauth]".
    iAssert (kmem_res γk fl) with "[Hflw Hauth]" as "HR".
    { iApply (kmem_res_close γk fl nullp []). rewrite /word_at.
      iSplitL "Hflw"; [iExact "Hflw" |]. iSplitR "Hauth"; [iPureIntro; reflexivity | iExact "Hauth"]. }
    iMod (inv_alloc lockN ⊤ (lock_inv γl lk (kmem_res γk fl)) with "[Hlock Hlocked HR]") as "#Hkmem".
    { iNext. iExists (mword_of_int 0 : mword 32). rewrite /lock_word.
      iSplitL "Hlock"; [iExact "Hlock" |]. iLeft. iSplit; [done |]. iFrame "Hlocked HR". }
    iModIntro.
    pose proof Hilcs as Hilcs_full. unfold callee_saved in Hilcs.
    destruct Hilcs as (Hilsp & Hiltp & Hils0 & Hils1 & Hils2 & Hils3 & Hils4 & Hils5 & Hils6 & Hils7 & Hils8 & Hils9 & Hils10 & Hils11).
    assert (Hmilsp : mil !!! Regidx csp_rs1 = spr) by (rewrite Hilsp; exact HR7sp).
    assert (Hmiltp : mil !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)) by (rewrite Hiltp; exact HR7tp).
    (* ===== compute a1 = PHYSTOP, a0 = end (0x1c..0x24), then jal freerange ===== *)
    (* +0x1c li a1,17 *)
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x1c)) (mword_of_int 11 : mword 5) (mword_of_int 17 : mword 6) (mword_of_int 17 : mword 64)
              mil (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R8 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int 17 : mword 64)]> mil).
    assert (Hpp1e : add_vec_int (mword_of_int (KI + 0x1c) : mword 64) 2 = mword_of_int (KI + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e slli a1,a1,27 *)
    iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x1e)) (Regidx (mword_of_int 11)) (mword_of_int 11 : mword 5) (mword_of_int 27 : mword 6)
              R8 (K - 2)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R9 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (shift_bits_left (R8 !!! Regidx (mword_of_int 11 : mword 5)) (subrange_vec_dec (mword_of_int 27 : mword 6) (Z.sub log2_xlen 1) 0))]> R8).
    assert (Hpp20 : add_vec_int (mword_of_int (KI + 0x1e) : mword 64) 2 = mword_of_int (KI + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    assert (HR9a1 : R9 !!! Regidx (mword_of_int 11 : mword 5) = phystop).
    { rewrite /R9 upd_eq. rewrite /R8 upd_eq.
      unfold phystop. apply bv_eq; vm_compute; reflexivity. }
    (* +0x20 auipc a0,0x23 *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x20)) (mword_of_int 10 : mword 5) (mword_of_int 35 : mword 20)
              R9 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi20 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R10 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (KI + 0x20) : mword 64) (auipc_off (mword_of_int 35 : mword 20)))]> R9).
    assert (Hpp24 : add_vec_int (mword_of_int (KI + 0x20) : mword 64) 4 = mword_of_int (KI + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* +0x24 addi a0,a0,-1474  (a0 := end) *)
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x24)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 2622 : mword 12)
              R10 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi24 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R11 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R10 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2622 : mword 12)))]> R10).
    assert (Hpp28 : add_vec_int (mword_of_int (KI + 0x24) : mword 64) 4 = mword_of_int (KI + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    assert (HR11a0 : R11 !!! Regidx (mword_of_int 10 : mword 5) = endaddr).
    { rewrite /R11 upd_eq. rewrite /R10 upd_eq.
      unfold endaddr. apply bv_eq; vm_compute; reflexivity. }
    assert (HR11a1 : R11 !!! Regidx (mword_of_int 11 : mword 5) = phystop).
    { rewrite /R11 upd_ne; [| vm_compute; discriminate].
      rewrite /R10 upd_ne; [exact HR9a1 | vm_compute; discriminate]. }
    assert (HR11sp : R11 !!! Regidx csp_rs1 = spr).
    { rewrite /R11 upd_ne; [| vm_compute; discriminate].
      rewrite /R10 upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [exact Hmilsp | vm_compute; discriminate]. }
    assert (HR11tp : R11 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /R11 upd_ne; [| vm_compute; discriminate].
      rewrite /R10 upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [exact Hmiltp | vm_compute; discriminate]. }
    (* +0x28 jal ra,freerange *)
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x28)) (mword_of_int 1 : mword 5) (mword_of_int 2097040 : mword 21)
              R11 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi28 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R12 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KI + 0x28) : mword 64) 4)]> R11).
    assert (Htgtfr : add_vec (mword_of_int (KI + 0x28) : mword 64) (sign_extend' 64 (mword_of_int 2097040 : mword 21)) = mword_of_int KernelSyms.freerange) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtfr) in "Hpc".
    assert (HR12a0 : R12 !!! Regidx (mword_of_int 10 : mword 5) = endaddr)
      by (rewrite /R12 upd_ne; [exact HR11a0 | vm_compute; discriminate]).
    assert (HR12a1 : R12 !!! Regidx (mword_of_int 11 : mword 5) = phystop)
      by (rewrite /R12 upd_ne; [exact HR11a1 | vm_compute; discriminate]).
    assert (HR12sp : R12 !!! Regidx csp_rs1 = spr)
      by (rewrite /R12 upd_ne; [exact HR11sp | vm_compute; discriminate]).
    assert (HR12tp : R12 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5))
      by (rewrite /R12 upd_ne; [exact HR11tp | vm_compute; discriminate]).
    assert (HR12ra : R12 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KI + 0x28) : mword 64) 4)
      by (rewrite /R12; apply upd_eq).
    (* freerange(end, PHYSTOP) : consumes the pages into the lock, threads the count *)
    iApply (Freerange.wp_freerange_sconf γ root_ppn Φ γl γk lk fl R12 ps (K - 2) ncnt
              ltac:(lia) Hncnt
              ltac:(rewrite HR12tp; exact Hmycpu)
              ltac:(rewrite HR12ra; vm_compute; reflexivity)
              ltac:(reflexivity) ltac:(reflexivity)
              ltac:(rewrite HR12a1 HR12a0; exact Hprun)
              ltac:(rewrite HR12tp; exact Hnoffdat)
              ltac:(rewrite HR12tp; exact Hintdat)
              with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc Hkmem Hpages [Hqnoff] [Hqint] [Hcpu] [Havail] [-]").
    { iEval (rewrite HR12tp). iExact "Hqnoff". }
    { iEval (rewrite HR12tp). iExact "Hqint". }
    { iExact "Hcpu". }
    { iExact "Havail". }
    iIntros (mfr) "Hsc Hhs Hcg Hcnt Htlbinv Hpc %Hfrcs Hqnoff Hqint Hqcpu Havail".
    iEval (rewrite HR12tp) in "Hqnoff".
    iEval (rewrite HR12tp) in "Hqint".
    assert (Hpcfr : update_vec_dec (add_vec (R12 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (KI + 0x2c)).
    { rewrite HR12ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcfr) in "Hpc".
    pose proof Hfrcs as Hfrcs_full. unfold callee_saved in Hfrcs.
    destruct Hfrcs as (Hfrsp & Hfrtp & Hfrs0 & Hfrs1 & Hfrs2 & Hfrs3 & Hfrs4 & Hfrs5 & Hfrs6 & Hfrs7 & Hfrs8 & Hfrs9 & Hfrs10 & Hfrs11).
    assert (Hfrsp' : mfr !!! Regidx csp_rs1 = spr) by (rewrite Hfrsp; exact HR12sp).
    (* ===== EPILOGUE (0x2c..0x32): restore ra/s0, frame trade back (move_up 2), ret ===== *)
    assert (Hpp2e : add_vec_int (mword_of_int (KI + 0x28) : mword 64) 4 = mword_of_int (KI + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    (* +0x2c c.ldsp ra,8(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x2c)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              mfr (K - 2)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2c [Hras] [-]").
    { iEval (rewrite -Hb1 -Hfrsp') in "Hras". iExact "Hras". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hras".
    iEval (rewrite Hfrsp' Hb1) in "Hras".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mfr).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 upd_ne; [exact Hfrsp' | vm_compute; discriminate]).
    assert (Hpp2e' : add_vec_int (mword_of_int (KI + 0x2c) : mword 64) 2 = mword_of_int (KI + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e') in "Hpc".
    (* +0x2e c.ldsp s0,0(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x2e)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 2)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2e [Hs0s] [-]").
    { iEval (rewrite -Hb2 -HE1sp) in "Hs0s". iExact "Hs0s". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hs0s".
    iEval (rewrite HE1sp Hb2) in "Hs0s".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 upd_ne; [exact HE1sp | vm_compute; discriminate]).
    assert (Hpp30 : add_vec_int (mword_of_int (KI + 0x2e) : mword 64) 2 = mword_of_int (KI + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* Hras/Hs0s are already at [pa_stk sp0 1..2] -- ready for the frame rebuild *)
    (* +0x30 c.addi sp,16 -- the frame trade back (move_up 2) *)
    set (E3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    assert (HE3csp : E3 !!! Regidx csp_rs1 = sp0).
    { rewrite /E3 upd_eq. rewrite HE2sp. unfold regval_into_reg, spr, sp0.
      apply initlock_sp_cancel. }
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite -HE3csp /E3 upd_eq. reflexivity. }
    assert (Hpop : E2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv HE2sp. exact Hspr2. }
    iAssert (stack_own sp0 2) with "[Hras Hs0s]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hras"; [iExists _; iExact "Hras"|].
      iSplitL "Hs0s"; [iExists _; iExact "Hs0s"|]. done. }
    iEval (rewrite -Hwv) in "Hframe".
    assert (Hpopstk : stack_in_data (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2)
      by (rewrite Hwv; apply (stack_in_data_mono _ 4); [lia | exact Hsid4]).
    iApply (wp_caddi_sp_pop_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x30)) (mword_of_int 16 : mword 6) E2 (K - 2)%nat 2 Hpop Hpopstk
              with "Hsc Hhs Hcg Htlbinv Hpc Hi30 Hframe [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2) with E3.
    assert (Hpp32 : add_vec_int (mword_of_int (KI + 0x30) : mword 64) 2 = mword_of_int (KI + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* +0x32 c.ret *)
    assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq; reflexivity. }
    assert (Hretaligned : eq_vec (access_vec_dec (update_vec_dec (add_vec (E3 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HE3ra; exact Hretm).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (KI + 0x32)) (mword_of_int 1 : mword 5) E3 K
              ltac:(vm_compute; discriminate) Hretaligned
              with "Hsc Hhs Hcg Htlbinv Hpc Hi32 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hretf : update_vec_dec (add_vec (E3 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HE3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iApply ("Hcont" $! γl γk E3 with "Hsc Hhs Hcg Hcnt Htlbinv Hpc [%] Hkmem Havail Hqnoff Hqint [Hname] Hqcpu").
    2:{ iExists _; iExact "Hname". }
    (* callee_saved m E3: the two sub-calls preserve s1..s11/tp; the epilogue
       restores sp/s0, and ra (caller-saved) is irrelevant. *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
              E3 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N1 Nsp N8.
      pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq (mword_of_int 11 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na1.
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hfrcs_full c Hc).
      rewrite /R12 upd_ne; [| congruence].
      rewrite /R11 upd_ne; [| congruence].
      rewrite /R10 upd_ne; [| congruence].
      rewrite /R9 upd_ne; [| congruence].
      rewrite /R8 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hilcs_full c Hc).
      rewrite /R7 upd_ne; [| congruence].
      rewrite /R6 upd_ne; [| congruence].
      rewrite /R5 upd_ne; [| congruence].
      rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    unfold callee_saved.
    split. { rewrite HE3csp. reflexivity. }
    split. { apply Hthread; vm_compute; first [reflexivity | discriminate]. }
    split. { rewrite /E3 upd_ne; [| vm_compute; discriminate].
             rewrite /E2 upd_eq; reflexivity. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End WpSconfKinit.

End KinitProof.
