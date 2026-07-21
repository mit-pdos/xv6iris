(* WpSconfMemsetPage.v -- the PAGE-LEVEL memset WP over the SIE-agnostic sconf
   world.  [wp_memset_page_sconf] is the sconf-native mirror of
   [wp_memset_page] (WpMemsetPage.v): it composes the sconf prefix/loop/suffix
   (WpSconfMemset.v) at the fixed page count N = 4096, threading [sconf] +
   hart_state + [sie_cap γ root_ppn m n] + [tlb_inv_pt].  memset needs 2 of
   the [n] available stack slots for its own save frame (premise
   [(2 <= n)%nat]): the prefix's sp push carves them out of the capability,
   the suffix's sp pop feeds them back, so the caller gets [sie_cap] back at
   the same avail [n].  memset runs OUTSIDE the interrupt-disabled region, so
   it must be SIE-blind (interrupts absorbed) -- hence sconf, not the SIE=0
   smode_config engine. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import WpGpr.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore KernelText WpMemsetS.
Require Import WpMemsetInstr WpMemsetPage.
Require Import CalleeSaved.
Require Import StackOwn.
Require Import KallocInv.
Require Import IntrDefs.
Require Import IntrDefs.
Require Import WpSconfMemset.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Require Import KptTree.
Require Import Riscv.rv64d.
Import Defs.

Notation MS := KernelSyms.memset.

Section WpSconfMemsetPage.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_memset_page_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat) (cval : mword 64) :
    let a0_idx : mword 5 := mword_of_int 10 in
    let a1_idx : mword 5 := mword_of_int 11 in
    let a2_idx : mword 5 := mword_of_int 12 in
    let pcE := mword_of_int MS in
    let sp0 := m0 !!! Regidx csp_rs1 in
    let ra0 := m0 !!! Regidx (mword_of_int 1 : mword 5) in
    let p := m0 !!! Regidx a0_idx in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (2 <= n)%nat ->
    page_valid p ->
    m0 !!! Regidx a1_idx = cval ->
    m0 !!! Regidx a2_idx = (mword_of_int 4096 : mword 64) ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m0 n -∗ tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is pcE -∗
    page_own p -∗
    ( ∀ mfin,
      sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap_gpr γ root_ppn mfin n -∗ tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      page_own p -∗
      ⌜ callee_saved m0 mfin ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros a0_idx a1_idx a2_idx pcE sp0 ra0 p ret_tgt Hn Hpv Hcval Ha2 Hret0.
    set (ra_idx := (mword_of_int 1 : mword 5)).
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (a4_idx := (mword_of_int 14 : mword 5)).
    set (a5_idx := (mword_of_int 15 : mword 5)).
    set (imm_entry := (mword_of_int 48 : mword 6)).
    set (shamt_l := (mword_of_int 32 : mword 6)).
    set (shamt_r := (mword_of_int 32 : mword 6)).
    set (nzimm_s0 := (mword_of_int 4 : mword 8)).
    set (imm8_beqz := (mword_of_int 11 : mword 8)).
    set (imm_bne := (mword_of_int 0x1ffa : mword 13)).
    set (wval_add := add_vec (mword_of_int 4096 : mword 64) p).
    set (s00 := m0 !!! Regidx s0_idx).
    set (sp' := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1).
    set (m3 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2).
    set (m4 := <[Regidx a2_idx := regval_into_reg (shift_bits_left (m3 !!! Regidx a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3).
    set (m5 := <[Regidx a2_idx := regval_into_reg (shift_bits_right (m4 !!! Regidx a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4).
    set (m6 := <[Regidx a4_idx := regval_into_reg wval_add]> m5).
    pose proof (add_vec_frame_cancel) as Hframe.
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc Hpage Hcont".
    (* --- bridge [page_own p] to memset's per-byte buffer --- *)
    iEval (rewrite /page_own /byte_any) in "Hpage".
    iDestruct (bytes_choose 4096 0 (fun j b => ((pa_add p j) ↦ₘ b)%I) with "Hpage")
      as (olds) "Hpage".
    iAssert ([∗ list] j ∈ seq 0 4096, (ms_pa (ms_addr p j)) ↦ₘ olds j)%I
      with "[Hpage]" as "Hbuf".
    { iApply (big_sepL_impl with "Hpage"). iIntros "!>" (k j _) "H".
      rewrite ms_pa_ms_addr. iExact "H". }
    (* --- prefix/loop/suffix instr resources --- *)
    iPoseProof (minstr_cba with "Htext") as "Hi0".
    iPoseProof (minstr_cbc with "Htext") as "Hi2".
    iPoseProof (minstr_cbe with "Htext") as "Hi4".
    iPoseProof (minstr_cc0 with "Htext") as "Hi6".
    iPoseProof (minstr_cc2 with "Htext") as "Hi8".
    iPoseProof (minstr_cc4 with "Htext") as "Hi10".
    iPoseProof (minstr_cc6 with "Htext") as "Hi12".
    iPoseProof (minstr_cc8 with "Htext") as "Hi14".
    iPoseProof (minstr_cca with "Htext") as "Hi16".
    iPoseProof (minstr_cd8 with "Htext") as "HiL0".
    iPoseProof (minstr_cda with "Htext") as "HiL2".
    iPoseProof (minstr_cdc with "Htext") as "HiL4".
    iPoseProof (minstr_cde with "Htext") as "HiL6".
    (* the value-coupling premises for the prefix and the loop *)
    assert (Hn0 : eq_vec (m0 !!! Regidx a2_idx) zero_reg = false)
      by (rewrite Ha2; vm_compute; reflexivity).
    assert (Hvalue_add : add_vec (m5 !!! Regidx a2_idx) (m5 !!! Regidx a0_idx) = wval_add).
    { assert (HA : m5 !!! Regidx a2_idx = (mword_of_int 4096 : mword 64)).
      { unfold m5, m4, m3.
        rewrite upd_eq.
        rewrite upd_eq.
        unfold m2, m1.
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite Ha2. apply bv_eq; vm_compute; reflexivity. }
      assert (HB : m5 !!! Regidx a0_idx = p).
      { unfold m5, m4, m3, m2, m1.
        repeat (rewrite upd_ne; [| vm_compute; discriminate]).
        reflexivity. }
      rewrite HA HB. reflexivity. }
    assert (Hsp' : sp' = pa_stk sp0 2).
    { unfold sp', imm_entry, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    (* --- PREFIX: 0x00..0x10 --- *)
    iApply (wp_memset_prefix_sconf γ root_ppn Φ m0 n imm_entry shamt_l shamt_r nzimm_s0 imm8_beqz
              wval_add Hn Hsp' Hn0 Hvalue_add
              with "Hsc Hhs Hcg Htlbinv Hpc
                    Hi0 Hi2 Hi4 Hi6 Hi8 Hi10 Hi12 Hi14 Hi16 [-]").
    iIntros "Hsc Hhs Hcg Htlbinv Hpc Hbra Hbs0".
    change (<[Regidx a4_idx := regval_into_reg wval_add]> m5) with m6.
    (* pc at pcE+20 = memset+0x14 = loop top *)
    assert (Hpc1 : add_vec_int pcE 20 = mword_of_int (MS + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1) in "Hpc".
    (* loop-entry facts on m6 *)
    assert (Hcur : m6 !!! Regidx a5_idx = ms_addr p 0).
    { unfold m6, m5, m4, m3.
      rewrite upd_ne; [| vm_compute; discriminate].
      rewrite upd_ne; [| vm_compute; discriminate].
      rewrite upd_ne; [| vm_compute; discriminate].
      rewrite upd_eq.
      unfold regval_into_reg. rewrite add_vec_zero_l.
      unfold m2, m1.
      rewrite upd_ne; [| vm_compute; discriminate].
      rewrite upd_ne; [| vm_compute; discriminate].
      unfold ms_addr, p. change (Z.of_nat 0) with 0%Z. symmetry. exact (RiscvExtras.avi0 (m0 !!! Regidx a0_idx)). }
    assert (Hm4 : m6 !!! Regidx a4_idx = wval_add)
      by (unfold m6; rewrite upd_eq; unfold regval_into_reg; reflexivity).
    assert (Hm1 : m6 !!! Regidx a1_idx = cval).
    { unfold m6, m5, m4, m3, m2, m1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite -Hcval. reflexivity. }
    (* --- LOOP: 0x14..0x1a --- *)
    iApply (wp_memset_loop_sconf γ root_ppn Φ 4096 p wval_add cval a1_idx a4_idx a5_idx imm_bne
              olds (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(intros j; exact (ms_incr_step p j))
              ltac:(intros j Hj; exact (ms_cmp_page p j Hpv Hj))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              minstr_cce minstr_cd2 minstr_cd4
              4096 0%nat m6 ltac:(reflexivity) ltac:(lia) Hcur Hm4 Hm1
              with "Hsc Hhs Hcg Htlbinv Htext Hpc Hbuf [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbuf".
    set (m7 := <[Regidx a5_idx := regval_into_reg (ms_addr p 4096)]> m6).
    change (<[Regidx a5_idx := regval_into_reg (ms_addr p 4096)]> m6) with m7.
    assert (Hpc2 : add_vec_int (add_vec_int (mword_of_int (MS + 0x14) : mword 64) 6) 4 = (mword_of_int (MS + 0x1e) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2) in "Hpc".
    (* --- SUFFIX: 0x1e..0x24 --- *)
    (* the suffix operates on m7; spd = m7!!!csp = sp' *)
    assert (Hsuf_sp : m7 !!! Regidx csp_rs1 = sp').
    { unfold m7, m6, m5, m4, m3, m2.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold m1. rewrite upd_eq. reflexivity. }
    assert (Hsuf_ra : m7 !!! Regidx (mword_of_int 1 : mword 5) = ra0).
    { unfold m7, m6, m5, m4, m3, m2, m1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold ra0; reflexivity. }
    (* the suffix's ret target is built from ra0e := ra0, so [Hret0] IS its Hal0 *)
    iApply (wp_memset_suffix_sconf γ root_ppn Φ m7 (n - 2)%nat ra0 s00
              Hret0
              with "Hsc Hhs Hcg Htlbinv HiL0 HiL2 HiL4 HiL6 Hpc [Hbra] [Hbs0] [-]").
    { iEval (rewrite Hsuf_sp). iExact "Hbra". }
    { iEval (rewrite Hsuf_sp). iExact "Hbs0". }
    iIntros (mfin) "Hhs Hsc Hcg Htlbinv Hpc %Hmeq".
    assert (Hnk : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    (* rebuild page_own from the all-cbyte buffer *)
    iApply ("Hcont" $! mfin with "Hsc Hhs Hcg Htlbinv Hpc [Hbuf] [%]").
    - iEval (rewrite /page_own /byte_any).
      iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H".
      iEval (rewrite ms_pa_ms_addr) in "H". iExists _. iExact "H".
    - (* callee_saved m0 mfin: only sp/s0 moved *)
      assert (Hcatch : forall r : regidx,
                r <> Regidx (mword_of_int 1 : mword 5) -> r <> Regidx s0_idx -> r <> Regidx csp_rs1 ->
                r <> Regidx a5_idx -> r <> Regidx a2_idx -> r <> Regidx a4_idx ->
                m7 !!! r = m0 !!! r).
      { intros r Hra Hs0 Hcsp Ha5 Ha2r Ha4.
        unfold m7, m6, m5, m4, m3, m2, m1.
        rewrite upd_ne; [| exact Ha5].
        rewrite upd_ne; [| exact Ha4].
        rewrite upd_ne; [| exact Ha2r].
        rewrite upd_ne; [| exact Ha2r].
        rewrite upd_ne; [| exact Ha5].
        rewrite upd_ne; [| exact Hs0].
        rewrite upd_ne; [| exact Hcsp].
        reflexivity. }
      rewrite Hmeq.
      unfold callee_saved. repeat split.
      (* [regfile] insert/lookup on concrete regidx keys reduces by
         computation, so [repeat split] already discharges all the
         genuinely-unchanged callee-saved fields; only [x2 sp] (whose
         value really changes, via [Hframe]) survives as a goal. *)
      rewrite upd_eq. rewrite Hsuf_sp.
      unfold sp', imm_entry. apply Hframe.
  Qed.

End WpSconfMemsetPage.
