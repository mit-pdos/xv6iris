(* WpMemsetArray.v -- the GENERAL whole-function WP for the kernel's [memset],
   over the SIE-agnostic sconf world.  [wp_memset_sconf] composes the sconf
   prefix/loop/suffix (WpSconfMemset.v / SpecMemsetParts) at an ARBITRARY byte count
   [len], threading [sconf] + hart_state + [sie_cap γ root_ppn m n] +
   [tlb_inv_pt].  This is memset's real contract; the page-level spec
   (WpSconfMemsetPage) and walk's page-zeroing step are instances at len = 4096.

   Two pure facts generalize the page proof away from the fixed 4096:
   [slli32_srli32] (the source's [(unsigned int)n] count truncation is the
   identity for len < 2^32) and [ms_cmp_bound] (the loop's end-pointer compare
   reflects the offset compare, wraparound or not).  [len] is otherwise
   unconstrained: len = 0 takes the source's [n == 0] exit and the array may
   wrap the address space. *)
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
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore WpMemsetS.
Require Import WpMemsetInstr WpMemsetPage.
Require Import CalleeSaved.
Require Import StackOwn.
Require Import SpecMemsetParts.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Require Import Riscv.rv64d.
Require Import SpecMemset.
Import Defs.

(* ===================================================================== *)
(*  Pure helpers generalizing the page geometry to an arbitrary [len].    *)
(* ===================================================================== *)

(* the memset source computes the byte count as [(unsigned int)n], i.e.
   [n << 32 >> 32] in a 64-bit register; for a count that already fits in
   32 bits this round-trip is the identity. *)
Lemma slli32_srli32 (x : mword 64) :
  bv_unsigned x < 2 ^ 32 ->
  shift_bits_right
    (shift_bits_left x (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
    (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0) = x.
Proof.
  intro Hx.
  assert (Hl : shift_bits_left x (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftl x 32).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  assert (Hr : shift_bits_right (shiftl x 32) (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftr (shiftl x 32) 32).
  { unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hl Hr. apply bv_eq.
  unfold shiftl, shiftr, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_left, MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned bv_shiftl_unsigned.
  assert (H32 : bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 32)) = 32).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  rewrite H32.
  pose proof (bv_unsigned_in_range 64 x) as [Hx0 _].
  assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  assert (Hmul_nonneg : 0 <= bv_unsigned x * 2 ^ 32)
    by (apply Z.mul_nonneg_nonneg; [ exact Hx0 | rewrite E32; lia ]).
  assert (Hmul_lt : bv_unsigned x * 2 ^ 32 < 2 ^ 64)
    by (rewrite E32 in Hx |- *; rewrite E64; nia).
  rewrite Z.shiftl_mul_pow2; [| lia].
  assert (Hmod : bv_modulus (MachineWord.MachineWord.Z_idx 64) = 2 ^ 64)
    by (unfold bv_modulus; f_equal).
  rewrite bv_wrap_small; [| rewrite Hmod; split; [ exact Hmul_nonneg | exact Hmul_lt ] ].
  rewrite Z.shiftr_div_pow2; [| lia].
  rewrite Z.div_mul; [ reflexivity | rewrite E32; lia ].
Qed.

(* the loop's end-pointer compare [p+(j+1) =? p+len] reflects the offset
   compare [(j+1) =? len].  The two addresses differ by [len - (j+1)], which is
   a nonzero residue mod 2^64 for every 0 < j+1 < len < 2^64, so NO no-wrap
   assumption on [p .. p+len) is needed: if the array wraps the address space
   the cursor wraps with it, exactly as the caller's [pa_add]-indexed buffer
   does. *)
Lemma ms_cmp_bound (p : mword 64) (len j : nat) :
  Z.of_nat len < 2 ^ 64 -> (j < len)%nat ->
  neq_vec (ms_addr p (S j)) (add_vec (mword_of_int (Z.of_nat len) : mword 64) p)
    = negb (Nat.eqb (S j) len).
Proof.
  intros Hlen Hj.
  assert (Hmod64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite E64 in Hlen.
  (* both addresses, as the wrapped sum of the base and the offset *)
  assert (HxL : bv_unsigned (ms_addr p (S j)) = bv_wrap 64 (bv_unsigned p + Z.of_nat (S j))).
  { unfold ms_addr. rewrite add_vec_unsigned moi_unsigned.
    rewrite bv_wrap_add_idemp_r. reflexivity. }
  assert (HeL : bv_unsigned (add_vec (mword_of_int (Z.of_nat len) : mword 64) p)
              = bv_wrap 64 (bv_unsigned p + Z.of_nat len)).
  { rewrite add_vec_unsigned moi_unsigned.
    rewrite bv_wrap_add_idemp_l. f_equal. lia. }
  unfold neq_vec. f_equal.
  destruct (Nat.eqb_spec (S j) len) as [He | Hne].
  - apply eq_vec_true_iff. apply bv_eq. rewrite HxL HeL He. reflexivity.
  - apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
    rewrite HxL HeL in Hc. unfold bv_wrap in Hc.
    (* equal residues => the modulus divides [len - (j+1)], which is too small *)
    assert (Hd : (((bv_unsigned p + Z.of_nat len) - (bv_unsigned p + Z.of_nat (S j)))
                    mod bv_modulus 64 = 0)%Z).
    { rewrite Zminus_mod. rewrite Hc. rewrite Z.sub_diag. apply Zmod_0_l. }
    replace ((bv_unsigned p + Z.of_nat len) - (bv_unsigned p + Z.of_nat (S j)))%Z
      with (Z.of_nat len - Z.of_nat (S j))%Z in Hd by lia.
    rewrite Z.mod_small in Hd; [ lia | rewrite Hmod64; lia ].
Qed.

Module MemsetArrayProof (Memset : MEMSET_PARTS) : MEMSET.

Section WpMemsetArray.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (*  The zero-count arm: the c.beqz at +0x08 is taken straight to the    *)
  (*  epilogue, so no byte is written and the (empty) buffer comes back   *)
  (*  untouched.                                                          *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_memset_sconf_zero (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat) (cval : mword 64) (olds : nat -> bv 8)
    : wp_memset_sconf_body γ root_ppn Φ m0 n 0 cval olds.
  Proof.
    cbv beta delta [wp_memset_sconf_body].
    intros a0_idx a1_idx a2_idx pcE ra0 p ret_tgt cbyte Hn Hlen32 Hcval Ha2 Hret0.
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
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc Hbuf Hcont".
    iPoseProof (minstr_cba with "Htext") as "Hi0".
    iPoseProof (minstr_cbc with "Htext") as "Hi2".
    iPoseProof (minstr_cbe with "Htext") as "Hi4".
    iPoseProof (minstr_cc0 with "Htext") as "Hi6".
    iPoseProof (minstr_cc2 with "Htext") as "Hi8".
    iPoseProof (minstr_cd8 with "Htext") as "HiL0".
    iPoseProof (minstr_cda with "Htext") as "HiL2".
    iPoseProof (minstr_cdc with "Htext") as "HiL4".
    iPoseProof (minstr_cde with "Htext") as "HiL6".
    (* --- HEAD: 0x00..0x06 --- *)
    iApply (Memset.wp_memset_head_sconf γ root_ppn Φ m0 n imm_entry nzimm_s0 Hn Hsp'
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0 Hi2 Hi4 Hi6 [-]").
    iIntros "Hsc Hhs Hcg Htlbinv Hpc Hbra Hbs0".
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
    iApply (Memset.wp_memset_skip_sconf γ root_ppn Φ m2 (n - 2)%nat imm8_beqz Hz Htgt
              with "Hsc Hhs Hcg Htlbinv Hpc Hi8 [-]").
    iIntros "Hsc Hhs Hcg Htlbinv Hpc".
    (* --- SUFFIX: 0x1e..0x24 --- *)
    assert (Hsuf_sp : m2 !!! Regidx csp_rs1 = sp').
    { unfold m2. rewrite upd_ne; [| vm_compute; discriminate].
      unfold m1. apply upd_eq. }
    iApply (Memset.wp_memset_suffix_sconf γ root_ppn Φ m2 (n - 2)%nat ra0 s00
              Hret0
              with "Hsc Hhs Hcg Htlbinv HiL0 HiL2 HiL4 HiL6 Hpc [Hbra] [Hbs0] [-]").
    { iEval (rewrite Hsuf_sp). iExact "Hbra". }
    { iEval (rewrite Hsuf_sp). iExact "Hbs0". }
    iIntros (mfin) "Hhs Hsc Hcg Htlbinv Hpc %Hmeq".
    assert (Hnk : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    iApply ("Hcont" $! mfin with "Hsc Hhs Hcg Htlbinv Hpc [Hbuf] [%]").
    - (* the buffer is empty at len = 0 *) iExact "Hbuf".
    - (* callee_saved m0 mfin: only sp/s0 moved, and both are restored *)
      rewrite Hmeq.
      unfold callee_saved. repeat split.
      rewrite upd_eq. rewrite Hsuf_sp.
      unfold sp', imm_entry. apply add_vec_frame_cancel.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The positive-count arm: c.beqz falls through into the count setup   *)
  (*  and the byte-fill loop.                                             *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_memset_sconf_pos (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat) (len : nat) (cval : mword 64) (olds : nat -> bv 8)
    : (0 < len)%nat -> wp_memset_sconf_body γ root_ppn Φ m0 n len cval olds.
  Proof.
    intro Hlen0.
    cbv beta delta [wp_memset_sconf_body].
    intros a0_idx a1_idx a2_idx pcE ra0 p ret_tgt cbyte Hn Hlen32 Hcval Ha2 Hret0.
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
    pose proof (add_vec_frame_cancel) as Hframe.
    (* [bv_unsigned] of the count literal, used repeatedly *)
    assert (Hlen64 : Z.of_nat len < 2 ^ 64)
      by (apply (Z.lt_trans _ (2 ^ 32)); [ exact Hlen32 | vm_compute; reflexivity ]).
    assert (Hlenu : bv_unsigned (mword_of_int (Z.of_nat len) : mword 64) = Z.of_nat len).
    { rewrite moi_unsigned. apply bv_wrap_small.
      unfold bv_modulus; simpl. split; [ lia | apply (Z.lt_trans _ (2 ^ 32)); [ lia | vm_compute; reflexivity ] ]. }
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc Hbuf0 Hcont".
    (* --- bridge the [pa_add]-indexed buffer to memset's [ms_pa (ms_addr)] one --- *)
    iAssert ([∗ list] j ∈ seq 0 len, (ms_pa (ms_addr p j)) ↦ₘ olds j)%I
      with "[Hbuf0]" as "Hbuf".
    { iApply (big_sepL_impl with "Hbuf0"). iIntros "!>" (k j _) "H".
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
    iApply (Memset.wp_memset_head_sconf γ root_ppn Φ m0 n imm_entry nzimm_s0 Hn Hsp'
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0 Hi2 Hi4 Hi6 [-]").
    iIntros "Hsc Hhs Hcg Htlbinv Hpc Hbra Hbs0".
    (* --- SETUP: 0x08..0x10 (the count is nonzero: c.beqz falls through) --- *)
    iApply (Memset.wp_memset_setup_sconf γ root_ppn Φ m2 (n - 2)%nat shamt_l shamt_r imm8_beqz
              wval_add Hn0 Hvalue_add
              with "Hsc Hhs Hcg Htlbinv Hpc Hi8 Hi10 Hi12 Hi14 Hi16 [-]").
    iIntros "Hsc Hhs Hcg Htlbinv Hpc".
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
    iApply (Memset.wp_memset_loop_sconf γ root_ppn Φ len p wval_add cval a1_idx a4_idx a5_idx imm_bne
              olds (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(intros j; exact (ms_incr_step p j))
              ltac:(intros j Hj; exact (ms_cmp_bound p len j Hlen64 Hj))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              minstr_cce minstr_cd2 minstr_cd4
              len 0%nat m6 ltac:(reflexivity) ltac:(lia) Hcur Hm4 Hm1
              with "Hsc Hhs Hcg Htlbinv Htext Hpc Hbuf [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbuf".
    set (m7 := <[Regidx a5_idx := regval_into_reg (ms_addr p len)]> m6).
    change (<[Regidx a5_idx := regval_into_reg (ms_addr p len)]> m6) with m7.
    assert (Hpc2 : add_vec_int (add_vec_int (mword_of_int (MS + 0x14) : mword 64) 6) 4 = (mword_of_int (MS + 0x1e) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
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
    iApply (Memset.wp_memset_suffix_sconf γ root_ppn Φ m7 (n - 2)%nat ra0 s00
              Hret0
              with "Hsc Hhs Hcg Htlbinv HiL0 HiL2 HiL4 HiL6 Hpc [Hbra] [Hbs0] [-]").
    { iEval (rewrite Hsuf_sp). iExact "Hbra". }
    { iEval (rewrite Hsuf_sp). iExact "Hbs0". }
    iIntros (mfin) "Hhs Hsc Hcg Htlbinv Hpc %Hmeq".
    assert (Hnk : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    (* hand the all-cbyte buffer back directly (KEEP the written bytes) *)
    iApply ("Hcont" $! mfin with "Hsc Hhs Hcg Htlbinv Hpc [Hbuf] [%]").
    - iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H".
      iEval (rewrite ms_pa_ms_addr) in "H". iExact "H".
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
  Lemma wp_memset_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat) (len : nat) (cval : mword 64) (olds : nat -> bv 8)
    : wp_memset_sconf_body γ root_ppn Φ m0 n len cval olds.
  Proof.
    destruct len as [| len' ].
    - apply wp_memset_sconf_zero.
    - apply wp_memset_sconf_pos. lia.
  Qed.

End WpMemsetArray.

End MemsetArrayProof.
