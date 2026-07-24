(* ProofProcMapstacks.v -- whole-function proof of proc_mapstacks
   (kernel/proc.c): kalloc a page for each of the 64 process kernel stacks
   and kvmmap it at KSTACK(i).

   This file currently holds the VALIDATED arithmetic + instruction-WP
   foundation the whole-function proof rests on:
     - the magic-reciprocal KSTACK address bridge (srai/mul/slli/addw/sub),
     - sconf WP lemmas for the three instructions with no pre-existing
       leaf (SRAI, MUL, ADDW), built on the generic gpr-write engine,
     - the [va_i] svpn/alignment/range facts feeding KM.wp_kvmmap_sconf.
   The instruction-walk (sealed epilogue, fuel-inducted loop, prologue) and
   the sealed functor [ProcMapstacksProof (K : KALLOC) (KM : KVMMAP)] build
   on top of these; see the report/worklist. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad list_numbers bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras RiscvExec RiscvFetchExec.
Require Import SmodeCore RegFile WpGpr WpMmodeShiftiop WpMmodeMul WpMmodeLeafBase ExecCommon VcGen.
Require Import IntrDefs WpSmodeIntr WpSconfAlu.
Require Import WpLock CpuOwn.
Require Import InstrBytes KernelText.
Require Import PtTree PtBuild KptPt KvmMap.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ================================================================= *)
(* Pure arithmetic: the KSTACK address bridge.                        *)
(* ================================================================= *)


(* magic reciprocal fact *)
Lemma magic_recip : (45 * 0x4fa4fa4fa4fa4fa5 = 1 + 14 * 18446744073709551616)%Z.
Proof. vm_compute. reflexivity. Qed.

(* sint of a small nonnegative mword_of_int *)
Lemma sint_moi_small (z : Z) : (0 <= z < 2^63)%Z ->
  sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  assert (Hu : bv_unsigned (mword_of_int z : mword 64) = z).
  { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
    lia. }
  rewrite Hu. apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = 2^63) by reflexivity. rewrite Hhm. lia.
Qed.

Lemma moi64_unsigned (z : Z) :
  bv_unsigned (mword_of_int z : mword 64) = z `mod` 18446744073709551616.
Proof.
  unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. unfold bv_wrap.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma sub128_63 (x : mword (2*64)) :
  bv_unsigned (subrange_vec_dec x (64-1) 0) = bv_unsigned x `mod` 2^64.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (64 - 1 - 0 + 1)) with 64%N.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). reflexivity.
Qed.

Lemma sub128_127 (x : mword (0+2*64-1+1)) :
  bv_unsigned (subrange_vec_dec x (0+2*64-1) 0) = bv_unsigned x `mod` 2^128.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (0+2*64 - 1 - 0 + 1)) with 128%N.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 128) with (2^128). reflexivity.
Qed.

Lemma gsi128 (N : Z) : bv_unsigned (get_slice_int (2*64) N 0) = N `mod` 2^128.
Proof.
  rewrite get_slice_int_eta. unfold get_slice_int'.
  replace (2 * 64 >=? 0) with true by reflexivity. cbn [sumbool_of_bool].
  rewrite autocast_id. rewrite sub128_127.
  unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. unfold bv_wrap.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx (0+2*64-1+1)) = 2^128) as -> by (vm_compute; reflexivity).
  rewrite Zmod_mod. reflexivity.
Qed.

(* the MUL result value characterization *)
Lemma mult_low_unsigned (a b : mword 64) :
  bv_unsigned (mult_to_bits_half 64 Signed Signed a b Low)
  = (sint a * sint b) `mod` 2 ^ 64.
Proof.
  unfold mult_to_bits_half. cbn beta iota.
  unfold to_bits_truncate.
  rewrite autocast_id.
  rewrite sub128_63.
  rewrite gsi128.
  change (2 ^ 128) with (2 ^ 64 * 2 ^ 64).
  rewrite (Z.mod_mod_divide (sint a * sint b) (2^64*2^64) (2^64)); [reflexivity | exists (2^64); ring].
Qed.

(* the KSTACK mul step: (45*i) * magic ≡ i (mod 2^64) for i < 64 *)
Lemma kstack_mul_step (i : nat) : (i < 64)%nat ->
  mult_to_bits_half 64 Signed Signed
    (mword_of_int (45 * Z.of_nat i)) (mword_of_int 0x4fa4fa4fa4fa4fa5) Low
  = mword_of_int (Z.of_nat i).
Proof.
  intro Hi. apply bv_eq. rewrite mult_low_unsigned.
  rewrite (sint_moi_small (45 * Z.of_nat i) ltac:(split; [lia | change (2^63) with 9223372036854775808; lia])).
  rewrite (sint_moi_small 0x4fa4fa4fa4fa4fa5 ltac:(split; [lia | vm_compute; reflexivity])).
  rewrite moi64_unsigned. change 18446744073709551616 with (2^64).
  (* 45*i*magic = i + (i*14)*2^64 ≡ i mod 2^64 *)
  assert (Hprod : (45 * Z.of_nat i * 5738987045154082725
                   = Z.of_nat i + (Z.of_nat i * 14) * 2 ^ 64)%Z)
    by (change (2 ^ 64)%Z with 18446744073709551616%Z; ring).
  rewrite Hprod. rewrite Z_mod_plus_full. reflexivity.
Qed.


Lemma moi64_uns (z : Z) : (0 <= z < 18446744073709551616)%Z -> bv_unsigned (mword_of_int z : mword 64) = z.
Proof.
  intro. unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity). lia.
Qed.

Lemma bvsigned_moi_small (z : Z) : (0 <= z < 2^63)%Z -> bv_signed (mword_of_int z : mword 64) = z.
Proof. intro Hz. change (bv_signed ?x) with (sint x). apply sint_moi_small; exact Hz. Qed.

Lemma srai3 (z : Z) : (0 <= z < 9223372036854775808)%Z ->
  shift_bits_right_arith (mword_of_int z : mword 64) (subrange_vec_dec (mword_of_int 3 : mword 6) 5 0)
  = mword_of_int (z / 8).
Proof.
  intro Hz. apply bv_eq.
  unfold shift_bits_right_arith, arith_shiftr, with_word, get_word, MachineWord.MachineWord.arith_shift_right.
  rewrite bv_ashiftr_unsigned.
  replace (bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64)
                  (MachineWord.MachineWord.Z_idx (int_of_mword false (subrange_vec_dec (mword_of_int 3 : mword 6) 5 0))))) with 3
    by (vm_compute; reflexivity).
  rewrite (bvsigned_moi_small z ltac:(change (2^63)%Z with 9223372036854775808%Z; lia)).
  rewrite Z.shiftr_div_pow2; [| lia]. change (2^3) with 8.
  assert (Hdlt : 0 <= z / 8 < 18446744073709551616).
  { split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with z; [apply Z.div_le_upper_bound; lia | lia]. }
  rewrite (moi64_uns (z/8) ltac:(exact Hdlt)).
  apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. exact Hdlt.
Qed.

Lemma slli13 (z : Z) : (0 <= z)%Z -> (z * 8192 < 18446744073709551616)%Z ->
  shift_bits_left (mword_of_int z : mword 64) (subrange_vec_dec (mword_of_int 13 : mword 6) 5 0)
  = mword_of_int (z * 8192).
Proof.
  intros Hz0 Hz. apply bv_eq.
  unfold shift_bits_left, shiftl, with_word, get_word, MachineWord.MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  replace (bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64)
                  (MachineWord.MachineWord.Z_idx (int_of_mword false (subrange_vec_dec (mword_of_int 13 : mword 6) 5 0))))) with 13
    by (vm_compute; reflexivity).
  assert (Hzlt : z < 18446744073709551616) by nia.
  rewrite (moi64_uns z ltac:(lia)).
  rewrite Z.shiftl_mul_pow2; [| lia]. change (2^13) with 8192.
  rewrite (moi64_uns (z*8192) ltac:(lia)).
  apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  split; [apply Z.mul_nonneg_nonneg; lia | exact Hz].
Qed.

Require Import RiscvExtras.

(* sub_vec of two mword_of_int, no wrap *)
Lemma subvec_moi (x y : Z) : (0 <= y)%Z -> (y <= x)%Z -> (x < 18446744073709551616)%Z ->
  sub_vec (mword_of_int x : mword 64) (mword_of_int y : mword 64) = mword_of_int (x - y).
Proof.
  intros Hy Hyx Hx. apply bv_eq.
  assert (Hxy : (0 <= x - y < 18446744073709551616)%Z) by lia.
  unfold sub_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.sub.
  rewrite bv_sub_unsigned.
  rewrite (moi64_uns x ltac:(lia)). rewrite (moi64_uns y ltac:(lia)).
  rewrite (moi64_uns (x - y) ltac:(exact Hxy)).
  apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. exact Hxy.
Qed.

(* addw step: (8192*i) +w 8192 = 8192*(i+1), no truncation *)
Lemma addw_step (i : nat) : (i < 64)%nat ->
  sign_extend' 64 (add_vec (subrange_vec_dec (mword_of_int (8192 * Z.of_nat i) : mword 64) 31 0 : mword 32)
                           (subrange_vec_dec (mword_of_int 8192 : mword 64) 31 0 : mword 32))
  = mword_of_int (8192 * (Z.of_nat i + 1)).
Proof.
  intro Hi.
  assert (Hvb : (0 <= 8192 * (Z.of_nat i + 1) <= 524288)%Z).
  { split; [apply Z.mul_nonneg_nonneg; lia|].
    apply (Z.le_trans _ (8192 * 64)); [apply Z.mul_le_mono_nonneg_l; lia | apply Z.leb_le; vm_compute; reflexivity]. }
  apply bv_eq.
  rewrite <- !trunc32_subrange.
  rewrite !trunc32_mword_of_int.
  set (v := (8192 * (Z.of_nat i + 1))%Z) in *.
  rewrite (moi64_uns v ltac:(lia)).
  set (w := add_vec (mword_of_int (8192 * Z.of_nat i) : mword 32) (mword_of_int 8192 : mword 32)).
  assert (Hw : bv_unsigned w = v).
  { unfold w, v, add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned.
    assert (Ha : bv_unsigned (mword_of_int (8192 * Z.of_nat i) : mword 32) = 8192 * Z.of_nat i).
    { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
      rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
      change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 32))%Z with 4294967296%Z. lia. }
    assert (Hb : bv_unsigned (mword_of_int 8192 : mword 32) = 8192).
    { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
      rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
      change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 32))%Z with 4294967296%Z. lia. }
    rewrite Ha. rewrite Hb.
    replace (8192 * Z.of_nat i + 8192)%Z with (8192 * (Z.of_nat i + 1))%Z by lia.
    apply bv_wrap_small. unfold bv_modulus.
    change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 32))%Z with 4294967296%Z. lia. }
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  unfold bv_signed. rewrite Hw.
  assert (Hhm : bv_half_modulus (MachineWord.MachineWord.Z_idx 32) = 2147483648) by (vm_compute; reflexivity).
  rewrite bv_swrap_small; [| rewrite Hhm; lia].
  apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. lia.
Qed.

Definition va_i (i : nat) : mword 64 := mword_of_int (0x3FFFFFF000 - 8192 * (Z.of_nat i + 1)).

Lemma va_i_uns (i : nat) : (i < 64)%nat -> bv_unsigned (va_i i) = 0x3FFFFFF000 - 8192 * (Z.of_nat i + 1).
Proof.
  intro Hi. unfold va_i, mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
  split; [| lia]. assert (8192 * (Z.of_nat i + 1) <= 8192 * 64) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma va_i_svpn (i : nat) : (i < 64)%nat -> svpn_of (va_i i) = kstack_vpn i.
Proof.
  intro Hi. apply bv_eq.
  rewrite (svpn_of_unsigned_lo (va_i i) ltac:(rewrite uint_unsigned; rewrite (va_i_uns i Hi); assert (8192*(Z.of_nat i+1)<=8192*64) by (apply Z.mul_le_mono_nonneg_l; lia); lia)).
  rewrite uint_unsigned. rewrite (va_i_uns i Hi).
  rewrite (kstack_vpn_uns i Hi).
  rewrite Z.shiftr_div_pow2; [| lia]. change (2^12) with 4096.
  replace (0x3FFFFFF000 - 8192 * (Z.of_nat i + 1)) with ((0x3FFFFFF - 2 * (Z.of_nat i + 1)) * 4096) by lia.
  rewrite Z.div_mul; [| lia]. reflexivity.
Qed.

Lemma va_i_align (i : nat) : (i < 64)%nat -> subrange_vec_dec (va_i i) 11 0 = (zeros' 12 : mword 12).
Proof.
  intro Hi. apply bv_eq.
  rewrite subrange64_unsigned_11_0. rewrite (va_i_uns i Hi).
  change (2^12) with 4096.
  replace (0x3FFFFFF000 - 8192 * (Z.of_nat i + 1)) with ((0x3FFFFFF - 2 * (Z.of_nat i + 1)) * 4096) by lia.
  rewrite Z.mod_mul; [| lia]. vm_compute. reflexivity.
Qed.

Lemma va_i_range (i : nat) : (i < 64)%nat -> (uint (va_i i) + Z.of_nat 1 * 4096 <= 2 ^ 38)%Z.
Proof.
  intro Hi. rewrite uint_unsigned. rewrite (va_i_uns i Hi).
  change (2^38) with 274877906944.
  assert (8192 * 1 <= 8192 * (Z.of_nat i + 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

(* ================================================================= *)
(* Instruction WP lemmas for SRAI / MUL / ADDW (no pre-existing leaf) *)
(* ================================================================= *)

(* ---- SRAI exec leaf (mirror SRLI) ---- *)
Lemma exec_execute_SHIFTIOP_SRAI (shamt : mword 6) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (shift_bits_right_arith a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))) s = Some (tt, s') ->
  exec (execute (SHIFTIOP (shamt, rs1, rd, SRAI))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (SHIFTIOP (shamt, rs1, rd, SRAI))) with (execute_SHIFTIOP shamt rs1 rd SRAI).
  unfold execute_SHIFTIOP. cbn match.
  rewrite (exec_bind_Some _ _ _ (shift_bits_right_arith a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

Definition gpr_srai_val (rs1 : mword 5) (shamt : mword 6) (s : mstate) : mword 64 :=
  shift_bits_right_arith (gpr_src rs1 s) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0).

Lemma exec_execute_SHIFTIOP_SRAI_gpr (rs1 rd : mword 5) (shamt : mword 6) s :
  exec (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRAI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_srai_val rs1 shamt s))).
Proof.
  unfold gpr_srai_val, gpr_src.
  eapply exec_execute_SHIFTIOP_SRAI.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

(* ---- RTYPEW ADDW exec leaf ---- *)
Definition gpr_addw_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  sign_extend' 64 (add_vec (subrange_vec_dec (gpr_src rs1 s) 31 0 : mword 32)
                           (subrange_vec_dec (gpr_src rs2 s) 31 0 : mword 32)).

Lemma exec_execute_RTYPEW_ADDW_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, ADDW))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_addw_val rs2 rs1 s))).
Proof.
  unfold gpr_addw_val, gpr_src.
  change (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, ADDW)))
    with (execute_RTYPEW (Regidx rs2) (Regidx rs1) (Regidx rd) ADDW).
  unfold execute_RTYPEW. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

Section WpArith.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_srai_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (shamt : mword 6) (m : regfile) (n : nat) :
    uint rd <> 0 -> rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRAI)) -∗
    ( sie_cap_gpr γ (<[Regidx rd := regval_into_reg
        (shift_bits_right_arith (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) n -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ Φ pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRAI))
              (shift_bits_right_arith (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m n Hrd Hrdsp _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SRAI_gpr rd rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_srai_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_mul_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64) (m : regfile) (n : nat) :
    uint rd <> 0 -> rd <> csp_rs1 ->
    mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2))
      (m !!! Regidx rs1) (m !!! Regidx rs2) (mulop_mul.(mul_op_result_part)) = wval ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗ instr pc false (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul)) -∗
    ( sie_cap_gpr γ (<[Regidx rd := regval_into_reg wval]> m) n -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base γ Φ pc rd rs1 rs2
              (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul)) wval m n Hrd Hrdsp _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_MUL_gpr rs2 rs1 rd s_pc Hrd).
      unfold gpr_mul_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_addw_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5) (m : regfile) (n : nat) :
    uint rd <> 0 -> rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗ instr pc true (RTYPEW (Regidx rs2, Regidx rd, Regidx rd, ADDW)) -∗
    ( sie_cap_gpr γ (<[Regidx rd := regval_into_reg
        (sign_extend' 64 (add_vec (subrange_vec_dec (m !!! Regidx rd) 31 0 : mword 32)
                                  (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)))]> m) n -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ Φ pc rd rd rs2
              (RTYPEW (Regidx rs2, Regidx rd, Regidx rd, ADDW))
              (sign_extend' 64 (add_vec (subrange_vec_dec (m !!! Regidx rd) 31 0 : mword 32)
                                        (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)))
              m n Hrd Hrdsp _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPEW_ADDW_gpr rs2 rd rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addw_val, gpr_src. rewrite Hva Hvb. reflexivity.
  Qed.
End WpArith.
