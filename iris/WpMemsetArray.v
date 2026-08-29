(* WpMemsetArray.v -- the GENERAL whole-function WP for the kernel's [memset],
   over the SIE-agnostic sconf world.  [wp_memset_sconf] composes the sconf
   prefix/loop/suffix (ProofMemset.v / SpecMemsetParts) at an ARBITRARY byte count
   [len], threading the [sie_cap_gpr γ m n] bundle (sconf + hart_state +
   sie_cap + gpr_file).  This is memset's real contract; the page-level spec
   (ProofMemsetPage) and walk's page-zeroing step are instances at len = 4096.

   Two pure facts from ByteCursor.v generalize the page proof away from the
   fixed 4096: [slli32_srli32] (the source's [(unsigned int)n] count truncation
   is the identity for len < 2^32) and [pa_add_cmp_bound] (the loop's
   end-pointer compare reflects the offset compare, wraparound or not).  [len]
   is otherwise unconstrained: len = 0 takes the source's [n == 0] exit and the
   array may wrap the address space. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto ByteCursor.
Require Import RegFile WpNext.
Require Import WpMmodeLeafBase.
Require Import WpMemsetS.
Require Import RiscvExtras.
Require Import CodeMemset WpMemsetPage.
Require Import CalleeSaved.
Require Import StackOwn.
Require Import SpecMemsetParts.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Require Import Riscv.rv64d.
Require Import SpecMemset.
Require Import TsoCtx TsoCtxShim.   (* converted spec; shim = the interior
   seam to the UNCONVERTED parts (SpecMemsetParts) this proof composes *)
Require Import KernelRvcDecode.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Module MemsetArrayProof (Memset : MEMSET_PARTS) : MEMSET.

Section WpMemsetArray.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Context {kt : ktier}.
  Context {ktb : ktier}.
  Context `{!KtierLe ktb kt}.
  (* ------------------------------------------------------------------ *)
  (*  The zero-count arm: the c.beqz at +0x08 is taken straight to the    *)
  (*  epilogue, so no byte is written and the (empty) buffer comes back   *)
  (*  untouched.                                                          *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_memset_sconf_zero
      (m0 : regfile) (n : nat) (cval : mword 64) (olds : nat -> bv 8) (b : bool) (pcur : mword 64)
    : wp_memset_sconf_body kt ktb m0 n 0 cval olds b pcur.
  Proof.
    cbv beta delta [wp_memset_sconf_body].
    intros a0_idx a1_idx a2_idx pcE ra0 p ret_tgt cbyte Hn Hlen32 Hcval Ha2.
    pose (sp0 := (m0 !!! Regidx csp_rs1 : mword 64)).
    set (ra_idx := (mword_of_int 1 : mword 5)).
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (imm_entry := (mword_of_int 48 : mword 6)).
    set (nzimm_s0 := (mword_of_int 4 : mword 8)).
    set (imm8_beqz := (mword_of_int 11 : mword 8)).
    set (s00 := m0 !!! Regidx s0_idx).
    set (sp' := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1).
    assert (Hsp' : sp' = pa_stk sp0 2).
    { unfold sp', imm_entry, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    iIntros "Hcg #Htext Hpc Hbuf Hcont".
    (* --- HEAD: 0x00..0x06 --- *)
    iApply (Memset.wp_memset_head_sconf kt m0 n imm_entry nzimm_s0 b pcur Hn Hsp'
              with "Hcg Hpc [] [] [] [] [-]").
    { iApply (minstr_000 with "Htext"). }
    { iApply (minstr_002 with "Htext"). }
    { iApply (minstr_004 with "Htext"). }
    { iApply (minstr_006 with "Htext"). }
    iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc Hbra Hbs0".
    (* --- SKIP: the count is zero, so 0x08 branches to the epilogue --- *)
    assert (Hz : eq_vec (m2 !!! Regidx a2_idx) zero_reg = true).
    { unfold m2, m1.
      rewrite upd_ne; [| vm_compute; discriminate].
      rewrite upd_ne; [| vm_compute; discriminate].
      rewrite Ha2. vm_compute; reflexivity. }
    assert (Htgt : add_vec (add_vec_int (pcE : mword 64) 8)
                     (sign_extend' 64 (sign_extend' 13 (concat_vec imm8_beqz ('b"0"))))
                 = (mword_of_int (KernelSyms.memset + 0x1e) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (Memset.wp_memset_skip_sconf kt m2 (n - 2)%nat imm8_beqz b pcur Hz Htgt
              with "Hcg Hpc [] [-]").
    { iApply (minstr_008 with "Htext"). }
    iEval (rewrite /wp_next). iIntros (CID2 Hs2) "Hcg Hpc".
    (* --- SUFFIX: 0x1e..0x24 --- *)
    assert (Hsuf_sp : m2 !!! Regidx csp_rs1 = sp').
    { unfold m2. rewrite upd_ne; [| vm_compute; discriminate].
      unfold m1. apply upd_eq. }
    iApply (Memset.wp_memset_suffix_sconf kt m2 (n - 2)%nat ra0 s00 b pcur
              with "Hcg [] [] [] [] Hpc [Hbra] [Hbs0] [-]").
    { iApply (minstr_01e with "Htext"). }
    { iApply (minstr_020 with "Htext"). }
    { iApply (minstr_022 with "Htext"). }
    { iApply (minstr_024 with "Htext"). }
    { iEval (rewrite Hsuf_sp). iExact "Hbra". }
    { iEval (rewrite Hsuf_sp). iExact "Hbs0". }
    iEval (rewrite /wp_next). iIntros (CID3 Hs3 mfin) "Hcg Hpc %Hmeq".
    assert (Hnk : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    iSpecialize ("Hcont" $! CID3 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mfin with "Hcg Hpc [Hbuf] [%]").
    - (* the buffer is empty at len = 0 *) iExact "Hbuf".
    - (* callee_saved m0 mfin: only sp/s0 moved, and both are restored *)
      rewrite Hmeq.
      unfold callee_saved. repeat split.
      rewrite upd_eq. rewrite Hsuf_sp.
      unfold sp', imm_entry. apply frame_cancel_16.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The positive-count arm: c.beqz falls through into the count setup   *)
  (*  and the byte-fill loop.                                             *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_memset_sconf_pos
      (m0 : regfile) (n : nat) (len : nat) (cval : mword 64) (olds : nat -> bv 8) (b : bool) (pcur : mword 64)
    : (0 < len)%nat -> wp_memset_sconf_body kt ktb m0 n len cval olds b pcur.
  Proof.
    intro Hlen0.
    cbv beta delta [wp_memset_sconf_body].
    intros a0_idx a1_idx a2_idx pcE ra0 p ret_tgt cbyte Hn Hlen32 Hcval Ha2.
  pose (sp0 := (m0 !!! Regidx csp_rs1 : mword 64)).
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
    set (wval_add := add_vec (mword_of_int (Z.of_nat len) : mword 64) p).
    set (s00 := m0 !!! Regidx s0_idx).
    set (sp' := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1).
    set (m3 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2).
    set (m4 := <[Regidx a2_idx := regval_into_reg (shift_bits_left (m3 !!! Regidx a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3).
    set (m5 := <[Regidx a2_idx := regval_into_reg (shift_bits_right (m4 !!! Regidx a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4).
    set (m6 := <[Regidx a4_idx := regval_into_reg wval_add]> m5).
    pose proof (frame_cancel_16) as Hframe.
    (* [bv_unsigned] of the count literal, used repeatedly *)
    assert (Hlen64 : Z.of_nat len < 2 ^ 64)
      by (apply (Z.lt_trans _ (2 ^ 32)); [ exact Hlen32 | vm_compute; reflexivity ]).
    assert (Hlenu : bv_unsigned (mword_of_int (Z.of_nat len) : mword 64) = Z.of_nat len).
    { rewrite moi64_unsigned. apply bv_wrap_small.
      unfold bv_modulus; simpl. split; [ lia | apply (Z.lt_trans _ (2 ^ 32)); [ lia | vm_compute; reflexivity ] ]. }
    iIntros "Hcg #Htext Hpc Hbuf0 Hcont".
    (* --- bridge the [pa_add]-indexed buffer to memset's [ms_pa (ms_addr)] one --- *)
    iAssert ([∗ list] j ∈ seq 0 len, (ms_pa (ms_addr p j)) ↦ₘ[ktb] olds j)%I
      with "[Hbuf0]" as "Hbuf".
    { iApply (big_sepL_impl with "Hbuf0"). iIntros "!>" (k j _) "H".
      rewrite ms_pa_ms_addr. iExact "H". }
    (* --- prefix/loop/suffix instr resources --- *)
    (* the value-coupling premises for the setup and the loop *)
    assert (Hn0 : eq_vec (m2 !!! Regidx a2_idx) zero_reg = false).
    { unfold m2, m1.
      rewrite upd_ne; [| vm_compute; discriminate].
      rewrite upd_ne; [| vm_compute; discriminate].
      rewrite Ha2. apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
      rewrite Hlenu in Hc.
      assert (Hzr : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
      rewrite Hzr in Hc. lia. }
    assert (Hvalue_add : add_vec (m5 !!! Regidx a2_idx) (m5 !!! Regidx a0_idx) = wval_add).
    { assert (HA : m5 !!! Regidx a2_idx = (mword_of_int (Z.of_nat len) : mword 64)).
      { unfold m5, m4, m3.
        rewrite upd_eq.
        rewrite upd_eq.
        unfold m2, m1.
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite Ha2. apply slli32_srli32. rewrite Hlenu. exact Hlen32. }
      assert (HB : m5 !!! Regidx a0_idx = p).
      { unfold m5, m4, m3, m2, m1.
        repeat (rewrite upd_ne; [| vm_compute; discriminate]).
        reflexivity. }
      rewrite HA HB. reflexivity. }
    assert (Hsp' : sp' = pa_stk sp0 2).
    { unfold sp', imm_entry, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    (* --- HEAD: 0x00..0x06 --- *)
    iApply (Memset.wp_memset_head_sconf kt m0 n imm_entry nzimm_s0 b pcur Hn Hsp'
              with "Hcg Hpc [] [] [] [] [-]").
    { iApply (minstr_000 with "Htext"). }
    { iApply (minstr_002 with "Htext"). }
    { iApply (minstr_004 with "Htext"). }
    { iApply (minstr_006 with "Htext"). }
    iEval (rewrite /wp_next). iIntros (CID1 Hs1) "Hcg Hpc Hbra Hbs0".
    (* --- SETUP: 0x08..0x10 (the count is nonzero: c.beqz falls through) --- *)
    iApply (Memset.wp_memset_setup_sconf kt m2 (n - 2)%nat shamt_l shamt_r imm8_beqz
              wval_add b pcur Hn0 Hvalue_add
              with "Hcg Hpc [] [] [] [] [] [-]").
    { iApply (minstr_008 with "Htext"). }
    { iApply (minstr_00a with "Htext"). }
    { iApply (minstr_00c with "Htext"). }
    { iApply (minstr_00e with "Htext"). }
    { iApply (minstr_010 with "Htext"). }
    iEval (rewrite /wp_next). iIntros (CID2 Hs2) "Hcg Hpc".
    change (<[Regidx a4_idx := regval_into_reg wval_add]> m5) with m6.
    (* pc at pcE+20 = memset+0x14 = loop top *)
    assert (Hpc1 : add_vec_int pcE 20 = mword_of_int (KernelSyms.memset + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
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
    iApply (Memset.wp_memset_loop_sconf kt ktb len p wval_add cval a1_idx a4_idx a5_idx imm_bne
              olds (n - 2)%nat b pcur
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(intros j; exact (ms_incr_step p j))
              ltac:(intros j Hj; exact (pa_add_cmp_bound p len j Hlen64 Hj))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              (* the three tp exclusions are [SrcOk] instances now, resolved *)
              minstr_014 minstr_018 minstr_01a
              len 0%nat m6 ltac:(reflexivity) ltac:(lia) Hcur Hm4 Hm1
              with "Hcg Htext Hpc Hbuf [-]").
    iEval (rewrite /wp_next). iIntros (CID3 Hs3) "Hcg Hpc Hbuf".
    set (m7 := <[Regidx a5_idx := regval_into_reg (ms_addr p len)]> m6).
    change (<[Regidx a5_idx := regval_into_reg (ms_addr p len)]> m6) with m7.
    assert (Hpc2 : add_vec_int (add_vec_int (mword_of_int (KernelSyms.memset + 0x14) : mword 64) 6) 4 = (mword_of_int (KernelSyms.memset + 0x1e) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2) in "Hpc".
    (* --- SUFFIX: 0x1e..0x24 --- *)
    assert (Hsuf_sp : m7 !!! Regidx csp_rs1 = sp').
    { unfold m7, m6, m5, m4, m3, m2.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold m1. rewrite upd_eq. reflexivity. }
    assert (Hsuf_ra : m7 !!! Regidx (mword_of_int 1 : mword 5) = ra0).
    { unfold m7, m6, m5, m4, m3, m2, m1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold ra0; reflexivity. }
    iApply (Memset.wp_memset_suffix_sconf kt m7 (n - 2)%nat ra0 s00 b pcur
              with "Hcg [] [] [] [] Hpc [Hbra] [Hbs0] [-]").
    { iApply (minstr_01e with "Htext"). }
    { iApply (minstr_020 with "Htext"). }
    { iApply (minstr_022 with "Htext"). }
    { iApply (minstr_024 with "Htext"). }
    { iEval (rewrite Hsuf_sp). iExact "Hbra". }
    { iEval (rewrite Hsuf_sp). iExact "Hbs0". }
    iEval (rewrite /wp_next). iIntros (CID4 Hs4 mfin) "Hcg Hpc %Hmeq".
    assert (Hnk : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    (* hand the all-cbyte buffer back directly (KEEP the written bytes) *)
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mfin with "Hcg Hpc [Hbuf] [%]").
    - iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H".
      iEval (rewrite ms_pa_ms_addr) in "H".
      iExact "H".
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
      rewrite upd_eq. rewrite Hsuf_sp.
      unfold sp', imm_entry. apply Hframe.
  Qed.

  (* the two count arms, dispatched on [len]. *)
  Lemma wp_memset_sconf
      (m0 : regfile) (n : nat) (len : nat) (cval : mword 64) (olds : nat -> bv 8) (b : bool) (pcur : mword 64)
    : wp_memset_sconf_body kt ktb m0 n len cval olds b pcur.
  Proof.
    destruct len as [| len' ].
    - apply (wp_memset_sconf_zero).
    - apply (wp_memset_sconf_pos). lia.
  Qed.

End WpMemsetArray.

End MemsetArrayProof.
