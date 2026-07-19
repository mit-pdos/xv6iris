(* WpSconfKalloc.v -- kalloc over the SIE-agnostic sconf world (kalloc cone,
   stage 8).  The sconf mirror of [wp_kalloc] (WpKalloc.v): acquire -> load
   freelist head -> branch (empty: reclose+release+return null; nonempty:
   pop+release+memset(p,5,4096)+return p).  Both arms thread the counting
   token [intr_count] NET-ZERO (acquire n->S n, release S n->n).  sp moves
   only at prologue/epilogue (4-slot frame, 3 saves + padding), traded
   through sie_cap_move_down/_up 4; memset (nonempty arm, AFTER release, at
   the ambient level) runs SIE-blind via wp_memset_page_sconf. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText WpAuipc.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SRegime SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv WpKallocDecode.
Require Import WpMycpu WpLock.
Require Import VcGen.
Require Import KptTree.
Require Import IntrDefs WpIntrInv WpSmodeIntr.
Require Import WpIntenaBits.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSconfMemsetPage WpSconfAcquire WpSconfRelease.
Require Import WpSconfKfree.
Require Import WpKalloc.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Section WpSconfKalloc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation AK := KernelSyms.kalloc.

  Lemma wp_kalloc_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γl : gname) (fl : mword 64)
      (m : gmap regidx (mword 64))
      (cpuold : mword 64) (noffv intena_old : mword 32)
      (n : nat) (K : nat) :
    let pcE : mword 64 := mword_of_int AK in
    let sp0 := m !!! Regidx csp_rs1 in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
    let a_noff := add_vec cpuv (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_int := add_vec cpuv (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let a_cpu := add_vec (mword_of_int KernelSyms.kmem : mword 64) (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    let po_noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let po_noff_store := (autocast (T := mword) (subrange_vec_dec po_noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    (14 <= K)%nat ->
    eq_vec (cpuold : mword 64) cpuv = false ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    fl = mword_of_int (KernelSyms.kmem + 24) ->
    (neq_vec (sign_extend' 64 noffv) zero_reg = false <-> n = 0%nat) ->
    zopz0zKzJ_s zero_reg (sign_extend' 64 po_noff_store) = false ->
    eq_vec (sign_extend' 64
       (if eq_vec (sign_extend' 64 noffv) zero_reg then (zeros' 32) else intena_old)) zero_reg = true ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    intr_count γ root_ppn n -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    is_lock γl (mword_of_int KernelSyms.kmem) (kmem_res fl) -∗
    stack_own (pa_stk sp0 kv_frame_slots) K -∗
    a_noff ↦₄ noffv -∗
    a_int ↦₄ intena_old -∗
    a_cpu ↦₈ cpuold -∗
    ( ∀ mr,
      sconf γ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap γ root_ppn mr -∗
      intr_count γ root_ppn n -∗
      tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      gpr_file mr -∗
      ⌜ callee_saved m mr ⌝ -∗
      kalloc_post (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
      stack_own (pa_stk sp0 kv_frame_slots) K -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pcE sp0 ret_tgt cpuv a_noff a_int a_cpu po_noff_a5 po_noff_store
      HK Hcpune Hretm Hfl Hnoff_lvl Hnoffpos Hintena0.
    iIntros "Hsc Hhs Hcap Hcnt Htlbinv #Htext Hpc Hfile #Hlock Hdeep Hqnoff Hqint Hqcpu Hcont".
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iPoseProof (kai_00 with "Htext") as "Hi00".
    iPoseProof (kai_02 with "Htext") as "Hi02".
    iPoseProof (kai_04 with "Htext") as "Hi04".
    iPoseProof (kai_06 with "Htext") as "Hi06".
    iPoseProof (kai_08 with "Htext") as "Hi08".
    iPoseProof (kai_0a with "Htext") as "Hi0a".
    iPoseProof (kai_0e with "Htext") as "Hi0e".
    iPoseProof (kai_12 with "Htext") as "Hi12".
    (* ===== PROLOGUE: 4-slot frame trade + 3 saves (ra/s0/s1) + padding ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hsp1 : R1 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite /R1 lookup_total_insert. unfold regval_into_reg, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    iDestruct (stack_own_split_1 (pa_stk sp0 kv_frame_slots) 4 K ltac:(lia) with "Hdeep") as "[Hd4 Hdeep]".
    (* +0x00 c.addi16sp sp,-32 *)
    iApply (wp_caddi_sp_s_sconf γ root_ppn Φ pcE (mword_of_int 32 : mword 6) m (stack_own sp0 4)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi00 [Hd4] [-]").
    { iIntros "Hcap".
      iDestruct (sie_cap_move_down γ root_ppn m R1 4 Hsp1 with "Hd4 Hcap") as "[Hcap Hframe]".
      iFrame "Hcap Hframe". }
    iIntros "Hhs Hsc Hcap Hframe Htlbinv Hpc Hfile".
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1 lookup_total_insert; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vg4)  "Hg4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hg4".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (AK + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 vr24 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi02 Hr24 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (AK + 0x02) : mword 64) 2 = mword_of_int (AK + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 vr16 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi04 Hr16 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (AK + 0x04) : mword 64) 2 = mword_of_int (AK + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 vr8 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi06 Hr8 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (AK + 0x06) : mword 64) 2 = mword_of_int (AK + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    assert (Hra0v : m !!! Regidx (mword_of_int 1 : mword 5) = R1 !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    (* +0x08 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (AK + 0x08) : mword 64) 2 = mword_of_int (AK + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a auipc a0,0x11 *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x0a)) (mword_of_int 10 : mword 5) (mword_of_int 0x11 : mword 20)
              R2 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (R3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x0a) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R2).
    assert (Hpp0e : add_vec_int (mword_of_int (AK + 0x0a) : mword 64) 4 = mword_of_int (AK + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e addi a0,a0,2046  (a0 := &kmem) *)
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x0e)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x7f0 : mword 12)
              R3 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi0e [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (R4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x7f0 : mword 12)))]> R3).
    assert (HR4a0 : R4 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /R4 lookup_total_insert. rewrite /R3 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp12 : add_vec_int (mword_of_int (AK + 0x0e) : mword 64) 4 = mword_of_int (AK + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ===== ACQUIRE call (intr_count n -> S n, deep-10 lent) ===== *)
    (* +0x12 jal ra,acquire *)
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x12)) (mword_of_int 1 : mword 5) (mword_of_int 0xc8 : mword 21)
              R4 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (mA := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AK + 0x12) : mword 64) 4)]> R4).
    assert (Htgtacq : add_vec (mword_of_int (AK + 0x12) : mword 64) (sign_extend' 64 (mword_of_int 0xc8 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HmAsp : mA !!! Regidx csp_rs1 = spr).
    { rewrite /mA lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspR1. }
    assert (HmAtp : mA !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /mA lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HmAa0 : mA !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /mA lookup_total_insert_ne; [| vm_compute; discriminate]. exact HR4a0. }
    assert (HmAra : mA !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AK + 0x12) : mword 64) 4)
      by (rewrite /mA; apply lookup_total_insert).
    iDestruct (stack_own_split_1 (pa_stk spr kv_frame_slots) 10 (K-4) ltac:(lia) with "[Hdeep]") as "[Hd10 Hrest]".
    { assert (Hda : pa_stk (pa_stk sp0 kv_frame_slots) 4 = pa_stk spr kv_frame_slots).
      { unfold spr, sp0, pa_stk, add_vec_int, kv_frame_slots. rewrite !add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      iEval (rewrite Hda) in "Hdeep". iExact "Hdeep". }
    iApply (wp_acquire_sconf γ root_ppn Φ γl (kmem_res fl) mA
              cpuold noffv intena_old n
              ltac:(rewrite HmAtp; exact Hcpune)
              ltac:(rewrite HmAra; vm_compute; reflexivity)
              with "Hsc Hhs Hcap Hcnt Htlbinv Htext Hpc Hfile [Hlock] [Hqcpu] [Hqnoff] [Hqint] [Hd10] [-]").
    { iEval (rewrite HmAa0). iExact "Hlock". }
    { iEval (rewrite HmAa0). iExact "Hqcpu". }
    { iEval (rewrite HmAtp). iExact "Hqnoff". }
    { iEval (rewrite HmAtp). iExact "Hqint". }
    { iEval (rewrite HmAsp). iExact "Hd10". }
    iIntros (ms macq) "%Hmsfacts Hhs Hsc Hcap Htlbinv Hpc Hfile %Hacqpins Htok HRres Hacpu Hanoff Haint Hd10 Hcnt".
    iEval (rewrite HmAsp) in "Hd10".
    assert (Hpc16 : update_vec_dec (add_vec (mA !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AK + 0x16)).
    { rewrite HmAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc16) in "Hpc".
    (* recombine acquire's returned deep-10 with the leftover into deep-(K-4) *)
    iDestruct (stack_own_split_2 (pa_stk spr kv_frame_slots) 10 (K-4) ltac:(lia) with "[$Hd10 $Hrest]") as "Hdeep".
    admit.
  Admitted.

End WpSconfKalloc.
