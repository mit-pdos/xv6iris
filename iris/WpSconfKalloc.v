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
    let noff_ret := (autocast (T := mword) (subrange_vec_dec
        (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 po_noff_store)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
        (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
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
      a_cpu ↦₈ (zero_reg : mword 64) -∗
      a_noff ↦₄ noff_ret -∗
      (∃ vint : mword 32, a_int ↦₄ vint) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pcE sp0 ret_tgt cpuv a_noff a_int a_cpu po_noff_a5 po_noff_store noff_ret
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
    pose proof Hacqpins as Hacqpins_cs.
    iPoseProof (kai_16 with "Htext") as "Hi16".
    iPoseProof (kai_1a with "Htext") as "Hi1a".
    iPoseProof (kai_1e with "Htext") as "Hi1e".
    (* the noff-cancel identity (shared with kfree): release nv1 = sext noffv *)
    assert (Hnv1eq : sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 po_noff_store) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)
                     = sign_extend' 64 noffv)
      by (exact (kfree_nv1_cancel_pure noffv)).
    assert (Hcancel : neq_vec (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 po_noff_store) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)) zero_reg = false <-> n = 0%nat)
      by (rewrite Hnv1eq; exact Hnoff_lvl).
    (* ===== +0x16 auipc s1,0x11 ; +0x1a ld s1,head ; +0x1e beqz s1 ===== *)
    (* +0x16 auipc s1,0x11 *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x16)) (mword_of_int 9 : mword 5) (mword_of_int 0x11 : mword 20)
              macq ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (R6 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x16) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> macq).
    assert (Hs1R6 : R6 !!! Regidx (mword_of_int 9 : mword 5) = add_vec (mword_of_int (AK + 0x16) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))
      by (rewrite /R6; apply lookup_total_insert).
    assert (Hpp1a : add_vec_int (mword_of_int (AK + 0x16) : mword 64) 4 = mword_of_int (AK + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a ld s1,-2038(s1) : s1 := head *)
    iDestruct "HRres" as (head pages) "[Hflw Hchain]".
    assert (Hldaddr : add_vec (R6 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 0x7fc : mword 12)) = fl).
    { rewrite Hs1R6 Hfl. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_ld_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x1a)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 0x7fc : mword 12)
              R6 head ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi1a [Hflw] [-]").
    { iEval (rewrite -Hldaddr) in "Hflw". rewrite /word_at. iExact "Hflw". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hflw".
    iEval (rewrite Hldaddr) in "Hflw".
    set (R7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg head]> R6).
    assert (Hs1R7 : R7 !!! Regidx (mword_of_int 9 : mword 5) = head) by (rewrite /R7; apply lookup_total_insert).
    assert (Hpp1e : add_vec_int (mword_of_int (AK + 0x1a) : mword 64) 4 = mword_of_int (AK + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* map facts threaded to both release calls *)
    assert (Hmsp : macq !!! Regidx csp_rs1 = spr) by (rewrite (callee_saved_lookup Hacqpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HmAsp).
    assert (Hmtp : macq !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)) by (rewrite (callee_saved_lookup Hacqpins_cs (mword_of_int 4) ltac:(vm_compute; reflexivity)); exact HmAtp).
    (* +0x1e c.beqz s1,+0x4c : head=nullp -> empty ; else pop *)
    destruct pages as [|pg ps].
    - (* ===== EMPTY: head=nullp, taken to +0x4c ===== *)
      iDestruct "Hchain" as %Hhead.
      iApply (wp_cbeqz_taken_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x1e)) (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5)
                R7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs1R7 Hhead; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi1e [-]").
      iNext. iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      assert (Htgtbeq : add_vec (mword_of_int (AK + 0x1e) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 23 : mword 8) ('b"0")))) = mword_of_int (AK + 0x4c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtbeq) in "Hpc".
      iAssert (kmem_res fl) with "[Hflw]" as "HRres".
      { iApply (kmem_res_close fl head []). rewrite /word_at.
        iSplitL "Hflw"; [ iExact "Hflw" | iPureIntro; exact Hhead ]. }
      iPoseProof (kai_4c with "Htext") as "Hi4c".
      iPoseProof (kai_50 with "Htext") as "Hi50".
      iPoseProof (kai_54 with "Htext") as "Hi54".
      (* +0x4c auipc a0,0x11 *)
      iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x4c)) (mword_of_int 10 : mword 5) (mword_of_int 0x11 : mword 20)
                R7 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi4c [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (E1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x4c) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R7).
      assert (Hpp50 : add_vec_int (mword_of_int (AK + 0x4c) : mword 64) 4 = mword_of_int (AK + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp50) in "Hpc".
      (* +0x50 addi a0,a0,1980  (a0 := &kmem) *)
      iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x50)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x7ae : mword 12)
                E1 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi50 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (E2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (E1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x7ae : mword 12)))]> E1).
      assert (Ha0kmem2 : E2 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /E2 lookup_total_insert /E1 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (Hpp54 : add_vec_int (mword_of_int (AK + 0x50) : mword 64) 4 = mword_of_int (AK + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp54) in "Hpc".
      (* +0x54 jal ra,release *)
      iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x54)) (mword_of_int 1 : mword 5) (mword_of_int 0x10e : mword 21)
                E2 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi54 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (E3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AK + 0x54) : mword 64) 4)]> E2).
      assert (Htgtr2 : add_vec (mword_of_int (AK + 0x54) : mword 64) (sign_extend' 64 (mword_of_int 0x10e : mword 21)) = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtr2) in "Hpc".
      assert (HE3csp : E3 !!! Regidx csp_rs1 = spr).
      { rewrite /E3 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E2 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E1 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
        exact Hmsp. }
      assert (HE3tp : E3 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
      { rewrite /E3 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E2 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E1 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
        exact Hmtp. }
      assert (HE3a0 : E3 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /E3 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Ha0kmem2. }
      assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AK + 0x54) : mword 64) 4)
        by (rewrite /E3; apply lookup_total_insert).
      iDestruct (stack_own_split_1 (pa_stk spr kv_frame_slots) 10 (K-4) ltac:(lia) with "Hdeep") as "[Hd10 Hrest]".
      (* the cbeqz-taken iNext stripped [intr_count (S n)]'s inner later on the
         handler spec; re-fold it (the spec is persistent). *)
      iDestruct "Hcnt" as "(Htok0 & Hinvspec & HsepA & HscaA & HstvA)".
      iDestruct "Hinvspec" as (hA) "[#HiA #HsA]".
      iAssert (intr_count γ root_ppn (S n)) with "[Htok0 HsepA HscaA HstvA]" as "Hcnt".
      { iApply (intr_count_pack_S γ root_ppn n with "Htok0").
        iApply (intr_restore_intro γ root_ppn hA with "HiA HsA HsepA HscaA HstvA"). }
      iApply (wp_release_sconf γ root_ppn Φ γl (mword_of_int KernelSyms.kmem) (kmem_res fl) E3
                (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)))
                po_noff_store
                (if eq_vec (sign_extend' 64 noffv) zero_reg then po_intena_val ms else intena_old)
                n (dqi:=DfracOwn 1)
                ltac:(rewrite HE3a0; apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite HE3tp; apply eq_vec_true_iff; reflexivity)
                Hcancel Hnoffpos
                ltac:(rewrite HE3ra; vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Htext Hpc Hfile [Hlock] Htok HRres [Hacpu] [Hanoff] [Haint] [Hd10] Hcnt [-]").
      { iExact "Hlock". }
      { iEval (rewrite HmAa0 HmAtp) in "Hacpu". iEval (rewrite HE3a0). iExact "Hacpu". }
      { iEval (rewrite HmAtp) in "Hanoff". iEval (rewrite HE3tp). iExact "Hanoff". }
      { iEval (rewrite HmAtp) in "Haint". iEval (rewrite HE3tp). iExact "Haint". }
      { iEval (rewrite HE3csp). iExact "Hd10". }
      iIntros (mr) "Hhs Hsc Hcap Htlbinv Hpc Hfile %Hrelpins Hcpu2 Hnoff2 Hint2 Hd10 Hcnt".
      iEval (rewrite HE3csp) in "Hd10".
      iDestruct (stack_own_split_2 (pa_stk spr kv_frame_slots) 10 (K-4) ltac:(lia) with "[$Hd10 $Hrest]") as "Hdeep".
      assert (Hpc58 : update_vec_dec (add_vec (E3 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AK + 0x58)).
      { rewrite HE3ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc58) in "Hpc".
      pose proof Hrelpins as Hrelpins_cs.
      unfold callee_saved in Hrelpins.
      destruct Hrelpins as (Hmrcsp & Hmrtp & Hmrs0 & Hmrs1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      assert (HE3s1 : E3 !!! Regidx (mword_of_int 9 : mword 5) = nullp).
      { rewrite /E3 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E2 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E1 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hs1R7. exact Hhead. }
      iPoseProof (kai_58 with "Htext") as "Hi58".
      iPoseProof (kai_40 with "Htext") as "Hi40".
      iPoseProof (kai_42 with "Htext") as "Hi42".
      iPoseProof (kai_44 with "Htext") as "Hi44".
      iPoseProof (kai_46 with "Htext") as "Hi46".
      iPoseProof (kai_48 with "Htext") as "Hi48".
      iPoseProof (kai_4a with "Htext") as "Hi4a".
      (* +0x58 c.j +0x40 *)
      iApply (wp_cj_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x58))
                (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")))
                mr ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi58 [-]").
      iNext. iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      assert (Htgtj : add_vec (mword_of_int (AK + 0x58) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")))) = mword_of_int (AK + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtj) in "Hpc".
      (* +0x40 c.mv a0,s1  (a0 := s1 = nullp) *)
      iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x40)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                mr ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (P41 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mr !!! Regidx (mword_of_int 9 : mword 5)))]> mr).
      assert (HspP41 : P41 !!! Regidx csp_rs1 = spr).
      { rewrite /P41 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmrcsp HE3csp. reflexivity. }
      assert (Hpp42 : add_vec_int (mword_of_int (AK + 0x40) : mword 64) 2 = mword_of_int (AK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      iEval (rewrite HspR1) in "Hr24". iEval (rewrite HspR1) in "Hr16". iEval (rewrite HspR1) in "Hr8". iEval (rewrite HspR1) in "Hg4".
      (* +0x42 c.ldsp ra,24(sp) *)
      iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x42)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                P41 (R1 !!! Regidx (mword_of_int 1 : mword 5))
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi42 [Hr24] [-]").
      { iEval (rewrite HspP41). iExact "Hr24". }
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr24".
      iEval (rewrite HspP41) in "Hr24".
      set (P42 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> P41).
      assert (HspP42 : P42 !!! Regidx csp_rs1 = spr) by (rewrite /P42 lookup_total_insert_ne; [ exact HspP41 | vm_compute; discriminate ]).
      assert (Hpp44 : add_vec_int (mword_of_int (AK + 0x42) : mword 64) 2 = mword_of_int (AK + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* +0x44 c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x44)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                P42 (R1 !!! Regidx (mword_of_int 8 : mword 5))
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi44 [Hr16] [-]").
      { iEval (rewrite HspP42). iExact "Hr16". }
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr16".
      iEval (rewrite HspP42) in "Hr16".
      set (P43 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> P42).
      assert (HspP43 : P43 !!! Regidx csp_rs1 = spr) by (rewrite /P43 lookup_total_insert_ne; [ exact HspP42 | vm_compute; discriminate ]).
      assert (Hpp46 : add_vec_int (mword_of_int (AK + 0x44) : mword 64) 2 = mword_of_int (AK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* +0x46 c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x46)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                P43 (R1 !!! Regidx (mword_of_int 9 : mword 5))
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi46 [Hr8] [-]").
      { iEval (rewrite HspP43). iExact "Hr8". }
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr8".
      iEval (rewrite HspP43) in "Hr8".
      set (P44 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 9 : mword 5))]> P43).
      assert (HspP44 : P44 !!! Regidx csp_rs1 = spr) by (rewrite /P44 lookup_total_insert_ne; [ exact HspP43 | vm_compute; discriminate ]).
      assert (Hpp48 : add_vec_int (mword_of_int (AK + 0x46) : mword 64) 2 = mword_of_int (AK + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp48) in "Hpc".
      (* +0x48 c.addi16sp sp,32 -- move_up 4 *)
      set (P45 := <[Regidx csp_rs1 := regval_into_reg (add_vec (P44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P44).
      assert (HP45csp : P45 !!! Regidx csp_rs1 = sp0).
      { rewrite /P45 lookup_total_insert. rewrite HspP44. unfold spr, sp0. apply kalloc_sp_cancel. }
      assert (HupE : P44 !!! Regidx csp_rs1 = pa_stk (P45 !!! Regidx csp_rs1) 4).
      { rewrite HspP44 HP45csp. unfold spr, sp0, pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_caddi16sp_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x48)) (mword_of_int 2 : mword 6) P44
                (stack_own (pa_stk sp0 kv_frame_slots) 4)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi48 [Hr24 Hr16 Hr8 Hg4] [-]").
      { iIntros "Hcap".
        iAssert (stack_own (P45 !!! Regidx csp_rs1) 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe".
        { rewrite HP45csp. rewrite stack_own_slots. cbn [seq].
          iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
          iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
          iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
          iSplitL "Hg4";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hg4"|].
          done. }
        iDestruct (sie_cap_move_up γ root_ppn P44 P45 4 HupE with "Hframe Hcap") as "[Hcap Hdeep4]".
        iEval (rewrite HP45csp) in "Hdeep4". iFrame "Hcap Hdeep4". }
      iIntros "Hhs Hsc Hcap Hdeep4 Htlbinv Hpc Hfile".
      change (<[Regidx csp_rs1 := regval_into_reg (add_vec (P44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P44) with P45.
      assert (Hpp4a : add_vec_int (mword_of_int (AK + 0x48) : mword 64) 2 = mword_of_int (AK + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      assert (Hda2 : pa_stk (pa_stk sp0 kv_frame_slots) 4 = pa_stk spr kv_frame_slots).
      { unfold spr, sp0, pa_stk, add_vec_int, kv_frame_slots. rewrite !add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      iEval (rewrite -Hda2) in "Hdeep".
      iDestruct (stack_own_split_2 (pa_stk sp0 kv_frame_slots) 4 K ltac:(lia) with "[$Hdeep4 $Hdeep]") as "Hdeep".
      (* +0x4a c.ret *)
      assert (HP45ra : P45 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /P45 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P44 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P43 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P42 lookup_total_insert.
        rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      assert (HP45a0 : P45 !!! Regidx (mword_of_int 10 : mword 5) = nullp).
      { rewrite /P45 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P44 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P43 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P42 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P41 lookup_total_insert.
        rewrite Hmrs1 HE3s1. apply add_vec_zero_l. }
      assert (Hretaligned : eq_vec (access_vec_dec (update_vec_dec (add_vec (P45 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
        by (rewrite HP45ra; exact Hretm).
      iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x4a)) (mword_of_int 1 : mword 5) P45
                ltac:(vm_compute; discriminate) Hretaligned
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi4a [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      assert (Hretf : update_vec_dec (add_vec (P45 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
        by (rewrite HP45ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iApply ("Hcont" $! P45 with "Hsc Hhs Hcap Hcnt Htlbinv Hpc Hfile [%] [] Hdeep [Hcpu2] [Hnoff2] [Hint2]").
      3:{ iEval (rewrite HE3a0) in "Hcpu2". iExact "Hcpu2". }
      3:{ iEval (rewrite HE3tp) in "Hnoff2". iExact "Hnoff2". }
      3:{ iEval (rewrite HE3tp) in "Hint2". iExists _. iExact "Hint2". }
      { (* callee_saved m P45 *)
        assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
                  c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
                  c <> mword_of_int 9 -> c <> mword_of_int 10 ->
                  P45 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N1 N2 N8 N9 N10.
          let peel := (repeat (rewrite lookup_total_insert_ne; [ | congruence ])) in
          rewrite /P45 /P44 /P43 /P42 /P41; peel;
          rewrite (callee_saved_lookup Hrelpins_cs c Hcs);
          rewrite /E3 /E2 /E1 /R7 /R6; peel;
          rewrite (callee_saved_lookup Hacqpins_cs c Hcs);
          rewrite /mA /R4 /R3 /R2 /R1; peel;
          reflexivity. }
        unfold callee_saved.
        split.
        { rewrite /P45 lookup_total_insert.
          assert (HP44csp : P44 !!! Regidx csp_rs1 = spr) by exact HspP44.
          rewrite HP44csp. unfold regval_into_reg, spr. apply kalloc_sp_cancel. }
        split.
        { apply Hthread; vm_compute; first [reflexivity | discriminate]. }
        split.
        { rewrite /P45 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P44 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P43 lookup_total_insert.
          rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
        split.
        { rewrite /P45 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P44 lookup_total_insert.
          rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
        repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate]. }
      { rewrite /kalloc_post. iLeft. iPureIntro. exact HP45a0. }
    - (* ===== NONEMPTY: head=pg, pop + release + memset(p,5,4096) ===== *)
      iDestruct "Hchain" as "(-> & %Hpv & Hrun)".
      iDestruct "Hrun" as (nxt) "[Hrun Hchain]".
      iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x1e)) (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5)
                R7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs1R7; apply eq_vec_false_iff; intro Hpz;
                      apply (page_valid_ne_null pg Hpv); rewrite Hpz; apply bv_eq; vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      iEval (rewrite /run_page) in "Hrun".
      iDestruct "Hrun" as "[Hpnext Hprest]".
      iPoseProof (kai_20 with "Htext") as "Hi20".
      iPoseProof (kai_22 with "Htext") as "Hi22".
      iPoseProof (kai_26 with "Htext") as "Hi26".
      (* +0x20 c.ld a5,0(s1) : a5 := nxt *)
      assert (Hpaddr : add_vec (R7 !!! Regidx (mword_of_int 9 : mword 5))
                 (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))) = pg).
      { replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000"))) : mword 64)
          with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hs1R7. apply kv_addv_zero. }
      iApply (wp_cld_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
                R7 nxt ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi20 [Hpnext] [-]").
      { iEval (rewrite Hpaddr). rewrite /word_at. iExact "Hpnext". }
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hpnext".
      iEval (rewrite Hpaddr) in "Hpnext".
      set (R8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg nxt]> R7).
      assert (Hpp22 : add_vec_int (mword_of_int (AK + 0x20) : mword 64) 2 = mword_of_int (AK + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 auipc a4,0x11 *)
      iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x22)) (mword_of_int 14 : mword 5) (mword_of_int 0x11 : mword 20)
                R8 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi22 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (R9 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x22) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R8).
      assert (Ha4R9 : R9 !!! Regidx (mword_of_int 14 : mword 5) = add_vec (mword_of_int (AK + 0x22) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))
        by (rewrite /R9; apply lookup_total_insert).
      assert (Ha5R9 : R9 !!! Regidx (mword_of_int 15 : mword 5) = nxt).
      { rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate]. rewrite /R8; apply lookup_total_insert. }
      assert (Hpp26 : add_vec_int (mword_of_int (AK + 0x22) : mword 64) 4 = mword_of_int (AK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* +0x26 sd a5,2046(a4) : kmem.freelist := nxt *)
      assert (Hstaddr : add_vec (R9 !!! Regidx (mword_of_int 14 : mword 5)) (sign_extend' 64 (mword_of_int 0x7f0 : mword 12)) = fl).
      { rewrite Ha4R9 Hfl. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_sd_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x26)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 0x7f0 : mword 12)
                R9 pg with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi26 [Hflw] [-]").
      { iEval (rewrite -Hstaddr) in "Hflw". rewrite /word_at. iExact "Hflw". }
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hflw".
      rewrite Ha5R9. iEval (rewrite Hstaddr) in "Hflw".
      iAssert (kmem_res fl) with "[Hflw Hchain]" as "HRres".
      { iApply (kmem_res_close fl nxt ps). rewrite /word_at. iFrame "Hflw Hchain". }
      iAssert (page_own pg) with "[Hpnext Hprest]" as "Hpage".
      { iApply (run_page_page_own pg nxt). rewrite /run_page /word_at. iFrame "Hpnext Hprest". }
      assert (Hpp2a : add_vec_int (mword_of_int (AK + 0x26) : mword 64) 4 = mword_of_int (AK + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      iPoseProof (kai_2a with "Htext") as "Hi2a".
      iPoseProof (kai_2e with "Htext") as "Hi2e".
      (* +0x2a auipc a0,0x11 ; +0x2e addi a0,a0,2000 (a0 := &kmem) *)
      iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x2a)) (mword_of_int 10 : mword 5) (mword_of_int 0x11 : mword 20)
                R9 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi2a [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (R10 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x2a) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R9).
      assert (Hpp2e : add_vec_int (mword_of_int (AK + 0x2a) : mword 64) 4 = mword_of_int (AK + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x2e)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x7d0 : mword 12)
                R10 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi2e [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (R11 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R10 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x7d0 : mword 12)))]> R10).
      assert (Ha0kmem : R11 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /R11 lookup_total_insert /R10 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (Hpp32 : add_vec_int (mword_of_int (AK + 0x2e) : mword 64) 4 = mword_of_int (AK + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp32) in "Hpc".
      iPoseProof (kai_32 with "Htext") as "Hi32".
      (* +0x32 jal ra,release *)
      iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x32)) (mword_of_int 1 : mword 5) (mword_of_int 0x130 : mword 21)
                R11 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi32 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (R12 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AK + 0x32) : mword 64) 4)]> R11).
      assert (Htgtr : add_vec (mword_of_int (AK + 0x32) : mword 64) (sign_extend' 64 (mword_of_int 0x130 : mword 21)) = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtr) in "Hpc".
      assert (HR12csp : R12 !!! Regidx csp_rs1 = spr).
      { rewrite /R12 /R11 /R10 /R9 /R8 /R7 /R6;
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]); exact Hmsp. }
      assert (HR12tp : R12 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
      { rewrite /R12 /R11 /R10 /R9 /R8 /R7 /R6;
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]); exact Hmtp. }
      assert (HR12a0 : R12 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Ha0kmem. }
      assert (HR12ra : R12 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AK + 0x32) : mword 64) 4)
        by (rewrite /R12; apply lookup_total_insert).
      assert (HR12s1 : R12 !!! Regidx (mword_of_int 9 : mword 5) = pg).
      { rewrite /R12 /R11 /R10 /R9 /R8;
        repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]); exact Hs1R7. }
      iDestruct (stack_own_split_1 (pa_stk spr kv_frame_slots) 10 (K-4) ltac:(lia) with "Hdeep") as "[Hd10 Hrest]".
      iApply (wp_release_sconf γ root_ppn Φ γl (mword_of_int KernelSyms.kmem) (kmem_res fl) R12
                (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)))
                po_noff_store
                (if eq_vec (sign_extend' 64 noffv) zero_reg then po_intena_val ms else intena_old)
                n (dqi:=DfracOwn 1)
                ltac:(rewrite HR12a0; apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite HR12tp; apply eq_vec_true_iff; reflexivity)
                Hcancel Hnoffpos
                ltac:(rewrite HR12ra; vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Htext Hpc Hfile [Hlock] Htok HRres [Hacpu] [Hanoff] [Haint] [Hd10] Hcnt [-]").
      { iExact "Hlock". }
      { iEval (rewrite HmAa0 HmAtp) in "Hacpu". iEval (rewrite HR12a0). iExact "Hacpu". }
      { iEval (rewrite HmAtp) in "Hanoff". iEval (rewrite HR12tp). iExact "Hanoff". }
      { iEval (rewrite HmAtp) in "Haint". iEval (rewrite HR12tp). iExact "Haint". }
      { iEval (rewrite HR12csp). iExact "Hd10". }
      iIntros (mr) "Hhs Hsc Hcap Htlbinv Hpc Hfile %Hrelpins Hcpu2 Hnoff2 Hint2 Hd10 Hcnt".
      iEval (rewrite HR12csp) in "Hd10".
      iDestruct (stack_own_split_2 (pa_stk spr kv_frame_slots) 10 (K-4) ltac:(lia) with "[$Hd10 $Hrest]") as "Hdeep".
      assert (Hpc36 : update_vec_dec (add_vec (R12 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AK + 0x36)).
      { rewrite HR12ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc36) in "Hpc".
      pose proof Hrelpins as Hrelpins_cs.
      unfold callee_saved in Hrelpins.
      destruct Hrelpins as (Hmrcsp & Hmrtp & Hmrs0 & Hmrs1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      iPoseProof (kai_36 with "Htext") as "Hi36".
      iPoseProof (kai_38 with "Htext") as "Hi38".
      iPoseProof (kai_3a with "Htext") as "Hi3a".
      (* +0x36 c.lui a2,0x1 (a2:=4096) *)
      iApply (wp_clui_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x36)) (mword_of_int 12 : mword 5)
                (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
                mr ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(unfold luival; apply bv_eq; vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi36 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (Mlui := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 4096 : mword 64)]> mr).
      assert (Hpp38 : add_vec_int (mword_of_int (AK + 0x36) : mword 64) 2 = mword_of_int (AK + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      (* +0x38 c.li a1,5 *)
      iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x38)) (mword_of_int 11 : mword 5)
                (mword_of_int 5 : mword 6) (mword_of_int 5 : mword 64)
                Mlui ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi38 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (Mli := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int 5 : mword 64)]> Mlui).
      assert (Hpp3a : add_vec_int (mword_of_int (AK + 0x38) : mword 64) 2 = mword_of_int (AK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.mv a0,s1 (a0 := p) *)
      iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x3a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                Mli ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi3a [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (M3a := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (Mli !!! Regidx (mword_of_int 9 : mword 5)))]> Mli).
      assert (Hpp3c : add_vec_int (mword_of_int (AK + 0x3a) : mword 64) 2 = mword_of_int (AK + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      iPoseProof (kai_3c with "Htext") as "Hi3c".
      (* +0x3c jal ra,memset *)
      iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x3c)) (mword_of_int 1 : mword 5) (mword_of_int 0x15e : mword 21)
                M3a ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi3c [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (Mms := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AK + 0x3c) : mword 64) 4)]> M3a).
      assert (Htgtms : add_vec (mword_of_int (AK + 0x3c) : mword 64) (sign_extend' 64 (mword_of_int 0x15e : mword 21)) = mword_of_int KernelSyms.memset)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtms) in "Hpc".
      assert (HMmsa0 : Mms !!! Regidx (mword_of_int 10 : mword 5) = pg).
      { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M3a lookup_total_insert.
        rewrite /Mli lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mlui lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmrs1 HR12s1. apply add_vec_zero_l. }
      assert (HMmss1 : Mms !!! Regidx (mword_of_int 9 : mword 5) = pg).
      { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M3a lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mli lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mlui lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmrs1. exact HR12s1. }
      assert (HMmsa1 : Mms !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 5 : mword 64)).
      { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M3a lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mli lookup_total_insert. reflexivity. }
      assert (HMmsa2 : Mms !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int 4096 : mword 64)).
      { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M3a lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mli lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mlui lookup_total_insert. reflexivity. }
      assert (HMmsra : Mms !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (AK + 0x40)).
      { rewrite /Mms lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (HMmssp : Mms !!! Regidx csp_rs1 = spr).
      { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M3a lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mli lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mlui lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmrcsp. exact HR12csp. }
      (* split off deep-2 for memset *)
      assert (Hda3 : pa_stk (pa_stk sp0 kv_frame_slots) 4 = pa_stk spr kv_frame_slots).
      { unfold spr, sp0, pa_stk, add_vec_int, kv_frame_slots. rewrite !add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      iDestruct (stack_own_split_1 (pa_stk spr kv_frame_slots) 2 (K-4) ltac:(lia) with "Hdeep") as "[Hd2 Hrest]".
      iApply (wp_memset_page_sconf γ root_ppn Φ Mms (mword_of_int 5 : mword 64)
                ltac:(rewrite HMmsa0; exact Hpv) HMmsa1 HMmsa2
                ltac:(rewrite HMmsra; vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlbinv Htext Hpc Hfile [Hd2] [Hpage] [-]").
      { iEval (rewrite HMmssp). iExact "Hd2". }
      { iEval (rewrite HMmsa0). iExact "Hpage". }
      iIntros (mfp) "Hsc Hhs Hcap Htlbinv Hpc Hd2 Hpage Hfile %Hpinsf".
      iEval (rewrite HMmssp) in "Hd2".
      iEval (rewrite HMmsa0) in "Hpage".
      iDestruct (stack_own_split_2 (pa_stk spr kv_frame_slots) 2 (K-4) ltac:(lia) with "[$Hd2 $Hrest]") as "Hdeep".
      pose proof Hpinsf as Hpinsf_cs.
      unfold callee_saved in Hpinsf.
      destruct Hpinsf as (Hfsp & Hftp & Hfs0 & Hfs1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      assert (Hpc40 : update_vec_dec (add_vec (Mms !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AK + 0x40)).
      { rewrite HMmsra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc40) in "Hpc".
      assert (Hmfsp : mfp !!! Regidx csp_rs1 = spr) by (rewrite Hfsp HMmssp; reflexivity).
      iPoseProof (kai_40 with "Htext") as "Hi40".
      iPoseProof (kai_42 with "Htext") as "Hi42".
      iPoseProof (kai_44 with "Htext") as "Hi44".
      iPoseProof (kai_46 with "Htext") as "Hi46".
      iPoseProof (kai_48 with "Htext") as "Hi48".
      iPoseProof (kai_4a with "Htext") as "Hi4a".
      (* +0x40 c.mv a0,s1 (a0 := p) *)
      iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x40)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                mfp ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      set (Q41 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfp !!! Regidx (mword_of_int 9 : mword 5)))]> mfp).
      assert (HspQ41 : Q41 !!! Regidx csp_rs1 = spr) by (rewrite /Q41 lookup_total_insert_ne; [ exact Hmfsp | vm_compute; discriminate ]).
      assert (Hpp42 : add_vec_int (mword_of_int (AK + 0x40) : mword 64) 2 = mword_of_int (AK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      iEval (rewrite HspR1) in "Hr24". iEval (rewrite HspR1) in "Hr16". iEval (rewrite HspR1) in "Hr8". iEval (rewrite HspR1) in "Hg4".
      (* +0x42 c.ldsp ra,24(sp) *)
      iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x42)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                Q41 (R1 !!! Regidx (mword_of_int 1 : mword 5))
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi42 [Hr24] [-]").
      { iEval (rewrite HspQ41). iExact "Hr24". }
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr24".
      iEval (rewrite HspQ41) in "Hr24".
      set (Q42 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> Q41).
      assert (HspQ42 : Q42 !!! Regidx csp_rs1 = spr) by (rewrite /Q42 lookup_total_insert_ne; [ exact HspQ41 | vm_compute; discriminate ]).
      assert (Hpp44 : add_vec_int (mword_of_int (AK + 0x42) : mword 64) 2 = mword_of_int (AK + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* +0x44 c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x44)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                Q42 (R1 !!! Regidx (mword_of_int 8 : mword 5))
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi44 [Hr16] [-]").
      { iEval (rewrite HspQ42). iExact "Hr16". }
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr16".
      iEval (rewrite HspQ42) in "Hr16".
      set (Q43 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> Q42).
      assert (HspQ43 : Q43 !!! Regidx csp_rs1 = spr) by (rewrite /Q43 lookup_total_insert_ne; [ exact HspQ42 | vm_compute; discriminate ]).
      assert (Hpp46 : add_vec_int (mword_of_int (AK + 0x44) : mword 64) 2 = mword_of_int (AK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* +0x46 c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x46)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                Q43 (R1 !!! Regidx (mword_of_int 9 : mword 5))
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi46 [Hr8] [-]").
      { iEval (rewrite HspQ43). iExact "Hr8". }
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr8".
      iEval (rewrite HspQ43) in "Hr8".
      set (Q44 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 9 : mword 5))]> Q43).
      assert (HspQ44 : Q44 !!! Regidx csp_rs1 = spr) by (rewrite /Q44 lookup_total_insert_ne; [ exact HspQ43 | vm_compute; discriminate ]).
      assert (Hpp48 : add_vec_int (mword_of_int (AK + 0x46) : mword 64) 2 = mword_of_int (AK + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp48) in "Hpc".
      (* +0x48 c.addi16sp sp,32 -- move_up 4 *)
      set (Q45 := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q44).
      assert (HQ45csp : Q45 !!! Regidx csp_rs1 = sp0).
      { rewrite /Q45 lookup_total_insert. rewrite HspQ44. unfold spr, sp0. apply kalloc_sp_cancel. }
      assert (HupQ : Q44 !!! Regidx csp_rs1 = pa_stk (Q45 !!! Regidx csp_rs1) 4).
      { rewrite HspQ44 HQ45csp. unfold spr, sp0, pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_caddi16sp_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x48)) (mword_of_int 2 : mword 6) Q44
                (stack_own (pa_stk sp0 kv_frame_slots) 4)
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi48 [Hr24 Hr16 Hr8 Hg4] [-]").
      { iIntros "Hcap".
        iAssert (stack_own (Q45 !!! Regidx csp_rs1) 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe".
        { rewrite HQ45csp. rewrite stack_own_slots. cbn [seq].
          iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
          iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
          iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
          iSplitL "Hg4";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hg4"|].
          done. }
        iDestruct (sie_cap_move_up γ root_ppn Q44 Q45 4 HupQ with "Hframe Hcap") as "[Hcap Hdeep4]".
        iEval (rewrite HQ45csp) in "Hdeep4". iFrame "Hcap Hdeep4". }
      iIntros "Hhs Hsc Hcap Hdeep4 Htlbinv Hpc Hfile".
      change (<[Regidx csp_rs1 := regval_into_reg (add_vec (Q44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q44) with Q45.
      assert (Hpp4a : add_vec_int (mword_of_int (AK + 0x48) : mword 64) 2 = mword_of_int (AK + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      iEval (rewrite -Hda3) in "Hdeep".
      iDestruct (stack_own_split_2 (pa_stk sp0 kv_frame_slots) 4 K ltac:(lia) with "[$Hdeep4 $Hdeep]") as "Hdeep".
      (* +0x4a c.ret *)
      assert (HQ45ra : Q45 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /Q45 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q44 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q43 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q42 lookup_total_insert.
        rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      assert (HQ45a0 : Q45 !!! Regidx (mword_of_int 10 : mword 5) = pg).
      { rewrite /Q45 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q44 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q43 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q42 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q41 lookup_total_insert.
        rewrite Hfs1 HMmss1. apply add_vec_zero_l. }
      assert (Hretaligned : eq_vec (access_vec_dec (update_vec_dec (add_vec (Q45 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
        by (rewrite HQ45ra; exact Hretm).
      iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (AK + 0x4a)) (mword_of_int 1 : mword 5) Q45
                ltac:(vm_compute; discriminate) Hretaligned
                with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi4a [-]").
      iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
      assert (Hretf : update_vec_dec (add_vec (Q45 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
        by (rewrite HQ45ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iApply ("Hcont" $! Q45 with "Hsc Hhs Hcap Hcnt Htlbinv Hpc Hfile [%] [Hpage] Hdeep [Hcpu2] [Hnoff2] [Hint2]").
      3:{ iEval (rewrite HR12a0) in "Hcpu2". iExact "Hcpu2". }
      3:{ iEval (rewrite HR12tp) in "Hnoff2". iExact "Hnoff2". }
      3:{ iEval (rewrite HR12tp) in "Hint2". iExists _. iExact "Hint2". }
      { (* callee_saved m Q45 *)
        assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
                  c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
                  c <> mword_of_int 9 -> c <> mword_of_int 10 ->
                  c <> mword_of_int 11 -> c <> mword_of_int 12 ->
                  c <> mword_of_int 14 -> c <> mword_of_int 15 ->
                  Q45 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N1 N2 N8 N9 N10 N11 N12 N14 N15.
          let peel := (repeat (rewrite lookup_total_insert_ne; [ | congruence ])) in
          rewrite /Q45 /Q44 /Q43 /Q42 /Q41; peel;
          rewrite (callee_saved_lookup Hpinsf_cs c Hcs);
          rewrite /Mms /M3a /Mli /Mlui; peel;
          rewrite (callee_saved_lookup Hrelpins_cs c Hcs);
          rewrite /R12 /R11 /R10 /R9 /R8 /R7 /R6; peel;
          rewrite (callee_saved_lookup Hacqpins_cs c Hcs);
          rewrite /mA /R4 /R3 /R2 /R1; peel;
          reflexivity. }
        unfold callee_saved.
        split.
        { rewrite /Q45 lookup_total_insert.
          rewrite HspQ44. unfold regval_into_reg, spr. apply kalloc_sp_cancel. }
        split.
        { apply Hthread; vm_compute; first [reflexivity | discriminate]. }
        split.
        { rewrite /Q45 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q44 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q43 lookup_total_insert.
          rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
        split.
        { rewrite /Q45 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q44 lookup_total_insert.
          rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
        repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate]. }
      { rewrite /kalloc_post HQ45a0. iRight. iFrame "Hpage". iPureIntro. exact Hpv. }
  Qed.

End WpSconfKalloc.
