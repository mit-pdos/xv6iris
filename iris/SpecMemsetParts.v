(* SpecMemsetParts.v -- the PIECEMEAL interface of Memset (the prefix/loop/suffix
   parts), used internally to compose the general whole-function spec in
   SpecMemset.v.  This is NOT the external contract -- callers should use
   SpecMemset (MEMSET) instead.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be checked
   in parallel. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn KernelText.
Require Import IntrDefs.
Require Import WpMemsetS.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation MS := KernelSyms.memset.

Definition wp_memset_prefix_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (imm_entry shamt_l shamt_r : mword 6) (nzimm_s0 imm8_beqz : mword 8) (wval_add : mword 64) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let s0_idx : mword 5 := mword_of_int 8 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let a2_idx : mword 5 := mword_of_int 12 in
  let a4_idx : mword 5 := mword_of_int 14 in
  let a5_idx : mword 5 := mword_of_int 15 in
  let pcE := mword_of_int KernelSyms.memset in
  let sp0 : mword 64 := m0 !!! Regidx csp_rs1 in
  let sp' := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm_entry)) in
  let pa_ra := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
  let pa_s0 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
  let ra0 := m0 !!! Regidx ra_idx in
  let s00 := m0 !!! Regidx s0_idx in
  let m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0 in
  let m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1 in
  let m3 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2 in
  let m4 := <[Regidx a2_idx := regval_into_reg (shift_bits_left (m3 !!! Regidx a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3 in
  let m5 := <[Regidx a2_idx := regval_into_reg (shift_bits_right (m4 !!! Regidx a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4 in
  let m6 := <[Regidx a4_idx := regval_into_reg wval_add]> m5 in
  (2 <= n)%nat ->
  sp' = pa_stk sp0 2 ->
  eq_vec (m0 !!! Regidx a2_idx) zero_reg = false ->
  add_vec (m5 !!! Regidx a2_idx) (m5 !!! Regidx a0_idx) = wval_add ->
  sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m0 n -∗ tlb_inv_pt root_ppn -∗
  pc_is pcE -∗
  instr pcE true (ITYPE (sign_extend' 12 imm_entry, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
  instr (add_vec_int pcE 2) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx ra_idx, sp, 8)) -∗
  instr (add_vec_int pcE 4) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx s0_idx, sp, 8)) -∗
  instr (add_vec_int pcE 6) true (ITYPE (caddi4spn_imm nzimm_s0, sp, Regidx s0_idx, ADDI)) -∗
  instr (add_vec_int pcE 8) true (BTYPE (sign_extend' 13 (concat_vec imm8_beqz ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)) -∗
  instr (add_vec_int pcE 10) true (RTYPE (Regidx a0_idx, zreg, Regidx a5_idx, ADD)) -∗
  instr (add_vec_int pcE 12) true (SHIFTIOP (shamt_l, Regidx a2_idx, Regidx a2_idx, SLLI)) -∗
  instr (add_vec_int pcE 14) true (SHIFTIOP (shamt_r, Regidx a2_idx, Regidx a2_idx, SRLI)) -∗
  instr (add_vec_int pcE 16) false (RTYPE (Regidx a0_idx, Regidx a2_idx, Regidx a4_idx, ADD)) -∗
  ( sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m6 (n - 2) -∗ tlb_inv_pt root_ppn -∗
    pc_is (add_vec_int pcE 20) -∗
    pa_ra ↦₈ ra0 -∗ pa_s0 ↦₈ s00 -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Definition wp_memset_loop_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (N : nat) (p e cval : mword 64) (ra1 ra4 ra5 : mword 5) (imm_bne : mword 13) (olds : nat -> bv 8) (n : nat) :=
  let pc0 := mword_of_int (KernelSyms.memset + 0x14) in
  let pc4 := add_vec_int pc0 4 in
  let pc6 := add_vec_int pc0 6 in
  let cbyte := nth_byte (autocast (T := mword) (subrange_vec_dec cval (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 in
  (* register indices distinct from x0 *)
  uint ra1 <> 0 -> uint ra4 <> 0 -> uint ra5 <> 0 ->
  (* fetch: TLB slot 5 + geometry for each of the three instructions *)
  (* bne target = loop top pc0; only 2-alignment is needed (the C extension
     legalizes the bit1 = 1 target in the relocated image). *)
  add_vec pc6 (sign_extend' 64 imm_bne) = pc0 ->
  eq_vec (access_vec_dec pc0 0) ('b"0") = true ->
  (* store geometry (svpn := svpn_of a8) is derived internally at [wp_sb_s_pt]. *)
  (* pointer arithmetic: c.addi advances offset; bne compares a5+1 vs a4=e *)
  (forall j : nat, add_vec (ms_addr p j) ms_incr1 = ms_addr p (S j)) ->
  (forall j : nat, (j < N)%nat -> neq_vec (ms_addr p (S j)) e = negb (Nat.eqb (S j) N)) ->
  (* register indices of a1/a4 are distinct from a5 (so c.addi a5 leaves them) *)
  Regidx ra4 <> Regidx ra5 -> Regidx ra1 <> Regidx ra5 ->
  ra5 <> csp_rs1 ->
  (* the three loop instructions, fetched fresh each iteration from kernel_text *)
  (⊢ kernel_text -∗ instr pc0 false (STORE (mword_of_int 0, Regidx ra1, Regidx ra5, 1))) ->
  (⊢ kernel_text -∗ instr pc4 true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx ra5, Regidx ra5, ADDI))) ->
  (⊢ kernel_text -∗ instr pc6 false (BTYPE (imm_bne, Regidx ra4, Regidx ra5, BNE))) ->
  forall (rem off : nat) (m : regfile),
  (off + rem = N)%nat -> (1 <= rem)%nat ->
  m !!! Regidx ra5 = ms_addr p off ->
  m !!! Regidx ra4 = e ->
  m !!! Regidx ra1 = cval ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m n -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗
  pc_is pc0 -∗
  ([∗ list] j ∈ seq off rem, (ms_pa (ms_addr p j)) ↦ₘ olds j) -∗
  ( hart_state ↦ᵣ HART_ACTIVE tt -∗
    sconf γ -∗
    sie_cap_gpr γ root_ppn (<[Regidx ra5 := regval_into_reg (ms_addr p N)]> m) n -∗
    tlb_inv_pt root_ppn -∗
    pc_is (add_vec_int pc6 4) -∗
    ([∗ list] j ∈ seq off rem, (ms_pa (ms_addr p j)) ↦ₘ cbyte) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Definition wp_memset_suffix_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (M : regfile) (n : nat) (ra0e s00e : mword 64) :=
  let spd := M !!! Regidx csp_rs1 in
  let sp0up := add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) in
  let ret_tgt := update_vec_dec (add_vec ra0e (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn M n -∗ tlb_inv_pt root_ppn -∗
  instr (mword_of_int (KernelSyms.memset + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1 : mword 5), false, 8)) -∗
  instr (mword_of_int (KernelSyms.memset + 0x20) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8 : mword 5), false, 8)) -∗
  instr (mword_of_int (KernelSyms.memset + 0x22) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
  instr (mword_of_int (KernelSyms.memset + 0x24) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1 : mword 5), zreg)) -∗
  pc_is (mword_of_int (KernelSyms.memset + 0x1e) : mword 64) -∗
  add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈ ra0e -∗
  add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) ↦₈ s00e -∗
  ( ∀ mf,
    hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
    sie_cap_gpr γ root_ppn mf (n + 2) -∗ tlb_inv_pt root_ppn -∗
    pc_is ret_tgt -∗
    ⌜ mf = <[Regidx csp_rs1 := regval_into_reg sp0up]>
           (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]>
            (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M)) ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type MEMSET_PARTS.
  Parameter wp_memset_prefix_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (imm_entry shamt_l shamt_r : mword 6) (nzimm_s0 imm8_beqz : mword 8) (wval_add : mword 64),
      wp_memset_prefix_sconf_body γ root_ppn Φ m0 n imm_entry shamt_l shamt_r nzimm_s0 imm8_beqz wval_add.
  Parameter wp_memset_loop_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (N : nat) (p e cval : mword 64) (ra1 ra4 ra5 : mword 5) (imm_bne : mword 13) (olds : nat -> bv 8) (n : nat),
      wp_memset_loop_sconf_body γ root_ppn Φ N p e cval ra1 ra4 ra5 imm_bne olds n.
  Parameter wp_memset_suffix_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (M : regfile) (n : nat) (ra0e s00e : mword 64),
      wp_memset_suffix_sconf_body γ root_ppn Φ M n ra0e s00e.
End MEMSET_PARTS.
