(* WpHolding.v -- decode/leaf lemmas for xv6's holding() in S-mode: one
   [instr] lemma per instruction of holding() (hi_00/hi_02/hi_04/hi_06 for the
   fast-path prefix, his_08 .. his_2a for the full frame/mycpu()/compare
   sequence) plus the underlying decode/execute facts they build on
   (hdec_*, hexec_*, seqz_sub_neq, po_mycpu_out_a0, ...):

     holding @ 0x80000b94 (KernelInstrs.kernel_bytes):
       +0x0  411c  c.lw  a5,0(a0)     a5 := sext32(lk->locked)
       +0x2  e399  c.bnez a5,+0x8     NOT taken (locked = 0)
       +0x4  4501  c.li  a0,0         a0 := 0
       +0x6  8082  c.ret              return to ra

   These are consumed by WpHoldingInv.wp_holding_lockinv{,_locked}, the CSL
   holding() specs against [is_lock] that supersede the plain-ownership
   whole-function WP formerly proved in this file (see WpHoldingInv.v's
   header for the current top-level story). The composition follows
   WpMycpu.v; the c.bnez fall-through leaf [wp_cbnez_fall_s] mirrors
   WpMemsetS.wp_cbeqz_fall_s_config with BNE. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc WpGprLoad.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew WpKernelvecNew WpPushOff.
Require Import WpPushOffMem WpPushOffCsr WpMycpu WpPushOffTop WpAcquireMem.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode lemmas (podec-style; the tactics mirror WpPushOffTop's).        *)
(* ===================================================================== *)
Local Ltac h_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac h_close1 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; h_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

Local Ltac h_close0 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; h_ast
  | apply (exec_currentlyEnabled_Zca s HmisaC) ].

(* +0x0  0x411c  c.lw a5,0(a0) *)
Lemma hdec_lw s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x411c : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x2  0xe399  c.bnez a5,+0x8 *)
Lemma hdec_bnez s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe399 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 3, Cregidx (mword_of_int 7)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x4  0x4501  c.li a0,0 *)
Lemma hdec_li s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4501 : mword 16)) s
  = Some (C_LI (mword_of_int 0, Regidx (mword_of_int 10)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x6  0x8082  c.ret: reuse WpPushOffTop.podec_2a *)

(* the C_LW ExecuteAs expansion for imm 0 / a0-base / a5-dest *)
Lemma h_imm0 : zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")) = (mword_of_int 0 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma hexec_lw s :
  exec (execute (C_LW (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_LW. cbn zeta.
  rewrite exec_returnM. rewrite po_cr2. rewrite po_cr7. rewrite h_imm0. reflexivity.
Qed.

Lemma hexec_bnez (imm : mword 8) (rs : cregidx) s :
  exec (execute (C_BNEZ (imm, rs))) s
    = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg, creg2reg_idx rs, BNE)), s).
Proof. unfold execute. cbn match. unfold execute_C_BNEZ. apply exec_returnM. Qed.


(* ===================================================================== *)
(* holding()'s SLOW path (lock word nonzero): frame alloc, a5 := lk->cpu, *)
(* mycpu(), a0 := (lk->cpu == mycpu()), frame free, ret.                  *)
(*   +0x08 1101 c.addi sp,-32    +0x0a ec06 c.sdsp ra,24(sp)              *)
(*   +0x0c e822 c.sdsp s0,16(sp) +0x0e e426 c.sdsp s1,8(sp)               *)
(*   +0x10 1000 c.addi4spn s0,32 +0x12 691c c.ld a5,16(a0)                *)
(*   +0x14 84be c.mv s1,a5       +0x16 52d000ef jal ra,mycpu              *)
(*   +0x1a 40a48533 sub a0,s1,a0 +0x1e 00153513 seqz a0,a0                *)
(*   +0x22..0x2a: ldsp ra/s0/s1, addi16sp 32, ret                          *)
(* ===================================================================== *)

(* +0x12  0x691c  c.ld a5,16(a0) *)
Lemma hdec_ld s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x691c : mword 16)) s
  = Some (C_LD (mword_of_int 2, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

Lemma h_imm16 : zero_extend' 12 (concat_vec (mword_of_int 2 : mword 5) ('b"000")) = (mword_of_int 16 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma hexec_ld s :
  exec (execute (C_LD (mword_of_int 2, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 16, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_LD. cbn zeta.
  rewrite exec_returnM. rewrite po_cr2. rewrite po_cr7. rewrite h_imm16. reflexivity.
Qed.

Local Ltac h_dbase s Hpriv :=
  decode_pause_prefix s Hpriv;
  match goal with |- ?lhs = ?rhs =>
    let l := eval vm_compute in lhs in change_no_check (l = rhs) end;
  h_ast.

(* +0x16  0x52d000ef  jal ra,mycpu (offset +0xd2c) *)
Lemma hdec_jal_mycpu s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x52d000ef : mword 32)) s
  = Some (JAL (mword_of_int 0xd2c : mword 21, Regidx (mword_of_int 1)), s).
Proof. intro Hpriv. h_dbase s Hpriv. Qed.

(* +0x1a  0x40a48533  sub a0,s1,a0 *)
Lemma hdec_sub s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x40a48533 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 9), Regidx (mword_of_int 10), SUB), s).
Proof. intro Hpriv. h_dbase s Hpriv. Qed.

(* +0x1e  0x00153513  seqz a0,a0 (sltiu a0,a0,1) *)
Lemma hdec_seqz s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x00153513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLTIU), s).
Proof. intro Hpriv. h_dbase s Hpriv. Qed.

(* register-generic RTYPE SUB execute (mirror of WpGpr.exec_execute_RTYPE_ADD_gpr) *)
Definition gpr_sub_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  sub_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
          (if Z.eqb (uint rs2) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)).

Lemma exec_execute_RTYPE_SUB_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) SUB) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_sub_val rs2 rs1 s))).
Proof.
  unfold gpr_sub_val.
  unfold execute_RTYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ (gpr_sub_val rs2 rs1 s) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
      apply exec_returnm. }
  unfold gpr_sub_val.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  destruct (Z.eqb (uint rd) 0); apply exec_returnm.
Qed.

(* register-generic ITYPE SLTIU execute *)
Definition gpr_sltiu_val (rs1 : mword 5) (imm : mword 12) (s : mstate) : mword 64 :=
  zero_extend' 64 (bool_to_bit (zopz0zI_u
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    (sign_extend' 64 imm))).

Lemma exec_execute_ITYPE_SLTIU_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_sltiu_val rs1 imm s))).
Proof.
  change (execute (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)))
    with (execute_ITYPE imm (Regidx rs1) (Regidx rd) SLTIU).
  unfold execute_ITYPE. cbn zeta match.
  rewrite (exec_bind_Some _ _ _ (gpr_sltiu_val rs1 imm s) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
      apply exec_returnm. }
  unfold gpr_sltiu_val.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  destruct (Z.eqb (uint rd) 0); apply exec_returnm.
Qed.

(* seqz on (a - b) is 0 when a <> b *)
Lemma seqz_sub_neq (a b : mword 64) :
  eq_vec a b = false ->
  zero_extend' 64 (bool_to_bit (zopz0zI_u (sub_vec a b)
    (sign_extend' 64 (mword_of_int 1 : mword 12)))) = (mword_of_int 0 : mword 64).
Proof.
  intro Hne.
  replace (sign_extend' 64 (mword_of_int 1 : mword 12)) with (mword_of_int 1 : mword 64)
    by (apply bv_eq; vm_compute; reflexivity).
  assert (Hab : a <> b) by (apply eq_vec_false_iff; exact Hne).
  destruct (zopz0zI_u (sub_vec a b) (mword_of_int 1)) eqn:Hlt.
  - exfalso. apply Hab.
    unfold zopz0zI_u in Hlt.
    apply Z.ltb_lt in Hlt.
    change (uint (mword_of_int 1 : mword 64)) with 1 in Hlt.
    rewrite uint_unsigned in Hlt.
    pose proof (bv_unsigned_in_range _ (sub_vec a b)) as [Hlo _].
    assert (H0 : bv_unsigned (sub_vec a b) = 0) by lia.
    apply bv_eq.
    unfold sub_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.sub in H0.
    rewrite bv_sub_unsigned in H0.
    pose proof (bv_unsigned_in_range _ a) as Ha.
    pose proof (bv_unsigned_in_range _ b) as Hb.
    unfold bv_wrap in H0.
    assert (M : bv_modulus 64 = 18446744073709551616) by reflexivity.
    rewrite M in H0. rewrite M in Ha. rewrite M in Hb.
    apply Z.mod_divide in H0; [| lia].
    destruct H0 as [q Hq].
    assert (Hq0 : q = 0) by lia.
    lia.
  - apply bv_eq. vm_compute. reflexivity.
Qed.

(* the a0 slot of a mycpu call's output register file, in closed form *)
Lemma po_mycpu_out_a0 (P : mword 64) (m : gmap regidx (mword 64)) :
  po_mycpu_out P m !!! Regidx (mword_of_int 10 : mword 5)
  = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)).
Proof.
  unfold po_mycpu_out. cbv zeta.
  repeat first [ rewrite lookup_total_insert
               | rewrite lookup_total_insert_ne; [| vm_compute; discriminate] ].
  unfold mycpu_ret, mycpu_a5.
  reflexivity.
Qed.

Section WpHolding.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* c.bnez rs NOT taken (rs = 0): fall through to pc+2.  Mirrors          *)
  (* WpMemsetS.wp_cbeqz_fall_s_config with BEQ -> BNE.                     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_cbnez_fall_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    neq_vec (m !!! Regidx rd1) zero_reg = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Hrs Hrd1 Hcmp)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rd1 = Some (m !!! Regidx rd1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rd1 (m !!! Regidx rd1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      apply exec_execute_BTYPE_BNE_fall. unfold rvv.
      rewrite Lva.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  Lemma wp_cbnez_taken_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    let tgt := add_vec pc (sign_extend' 64 (sign_extend' 13 (concat_vec imm8 ('b"0")))) in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    neq_vec (m !!! Regidx rd1) zero_reg = true ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec tgt 1) = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is tgt -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros tgt HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Hrs Hrd1 Hcmp Hal0 Hal1.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rd1 = Some (m !!! Regidx rd1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rd1 (m !!! Regidx rd1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iMod (reg_update _ nextPC _ tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC tgt).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc.
      rewrite Hrs. change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : neq_vec (rvv rd1 s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact Hcmp. }
      epose proof (exec_execute_BTYPE_BNE_taken (sign_extend' 13 (concat_vec imm8 ('b"0")))
                     (zero_extend' 5 ('b"00")) rd1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. fold tgt in Hred.
      exact (Hred Hal0 Hal1). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc nextPC tgt).(sregs) = tgt)
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the four fast-path instructions.                    *)
  (* ------------------------------------------------------------------- *)
  Local Ltac mk_rvc4 A h w pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
    let Hsub := fresh "Hsub" in let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = true) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hsub : subrange_vec_dec w 15 0 = h) by (apply bv_eq; vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc4 pc h w H2al H4al Hrvc Hsub);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac mk_rvc2 A h pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
    let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = false) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 2)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte h j))
      by (intros j Hj;
          do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc2 pc h H2al H4al Hrvc);
      iApply (kernel_window_pc A h 2 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac mk_base A w pc ast decname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let Hnrvc := fresh "Hnrvc" in let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (Hnrvc : isRVC (subrange_vec_dec w 15 0) = false) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_Base w);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_base pc w H2al Hnrvc);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; apply decname; assumption ].

  Lemma hi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x0) : mword 64) true
      (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc4 (KernelSyms.holding + 0x0)%Z (mword_of_int 0x411c : mword 16) (mword_of_int 0xe399411c : mword 32)
    (mword_of_int (KernelSyms.holding + 0x0) : mword 64)
    (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) hdec_lw hexec_lw. Qed.

  Lemma hi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x2) : mword 64) true
      (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc2 (KernelSyms.holding + 0x2)%Z (mword_of_int 0xe399 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x2) : mword 64)
    (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) hdec_bnez hexec_bnez. Qed.

  Lemma hi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x4) : mword 64) true
      (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc4 (KernelSyms.holding + 0x4)%Z (mword_of_int 0x4501 : mword 16) (mword_of_int 0x80824501 : mword 32)
    (mword_of_int (KernelSyms.holding + 0x4) : mword 64)
    (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) hdec_li exec_execute_C_LI. Qed.

  Lemma hi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x6) : mword 64) true
      (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc2 (KernelSyms.holding + 0x6)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x6) : mword 64)
    (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) podec_2a exec_execute_C_JR. Qed.


  Lemma his_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x08) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc4 (KernelSyms.holding + 0x08)%Z (mword_of_int 0x1101 : mword 16) (mword_of_int 0xec061101 : mword 32)
    (mword_of_int (KernelSyms.holding + 0x08) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) podec_00 exec_execute_C_ADDI. Qed.

  Lemma his_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc2 (KernelSyms.holding + 0x0a)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) podec_02 exec_execute_C_SDSP. Qed.

  Lemma his_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc4 (KernelSyms.holding + 0x0c)%Z (mword_of_int 0xe822 : mword 16) (mword_of_int 0xe426e822 : mword 32)
    (mword_of_int (KernelSyms.holding + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) podec_04 exec_execute_C_SDSP. Qed.

  Lemma his_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc2 (KernelSyms.holding + 0x0e)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) podec_06 exec_execute_C_SDSP. Qed.

  Lemma his_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x10) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc4 (KernelSyms.holding + 0x10)%Z (mword_of_int 0x1000 : mword 16) (mword_of_int 0x691c1000 : mword 32)
    (mword_of_int (KernelSyms.holding + 0x10) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) podec_08 exec_execute_C_ADDI4SPN. Qed.

  Lemma his_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x12) : mword 64) true (LOAD (mword_of_int 16, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc2 (KernelSyms.holding + 0x12)%Z (mword_of_int 0x691c : mword 16)
    (mword_of_int (KernelSyms.holding + 0x12) : mword 64) (LOAD (mword_of_int 16, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)) hdec_ld hexec_ld. Qed.

  Lemma his_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x14) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc4 (KernelSyms.holding + 0x14)%Z (mword_of_int 0x84be : mword 16) (mword_of_int 0x00ef84be : mword 32)
    (mword_of_int (KernelSyms.holding + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)) podec_0e exec_execute_C_MV. Qed.

  Lemma his_16 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x16) : mword 64) false (JAL (mword_of_int 0xd2c : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.holding + 0x16)%Z (mword_of_int 0x52d000ef : mword 32)
    (mword_of_int (KernelSyms.holding + 0x16) : mword 64) (JAL (mword_of_int 0xd2c : mword 21, Regidx (mword_of_int 1))) hdec_jal_mycpu. Qed.

  Lemma his_1a : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x1a) : mword 64) false (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 9), Regidx (mword_of_int 10), SUB)).
  Proof. mk_base (KernelSyms.holding + 0x1a)%Z (mword_of_int 0x40a48533 : mword 32)
    (mword_of_int (KernelSyms.holding + 0x1a) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 9), Regidx (mword_of_int 10), SUB)) hdec_sub. Qed.

  Lemma his_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x1e) : mword 64) false (ITYPE (mword_of_int 1, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLTIU)).
  Proof. mk_base (KernelSyms.holding + 0x1e)%Z (mword_of_int 0x00153513 : mword 32)
    (mword_of_int (KernelSyms.holding + 0x1e) : mword 64) (ITYPE (mword_of_int 1, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLTIU)) hdec_seqz. Qed.

  Lemma his_22 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x22) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc2 (KernelSyms.holding + 0x22)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) podec_22 exec_execute_C_LDSP. Qed.

  Lemma his_24 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x24) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc4 (KernelSyms.holding + 0x24)%Z (mword_of_int 0x6442 : mword 16) (mword_of_int 0x64a26442 : mword 32)
    (mword_of_int (KernelSyms.holding + 0x24) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) podec_24 exec_execute_C_LDSP. Qed.

  Lemma his_26 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x26) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc2 (KernelSyms.holding + 0x26)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x26) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) podec_26 exec_execute_C_LDSP. Qed.

  Lemma his_28 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x28) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc4 (KernelSyms.holding + 0x28)%Z (mword_of_int 0x6105 : mword 16) (mword_of_int 0x80826105 : mword 32)
    (mword_of_int (KernelSyms.holding + 0x28) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) podec_28 exec_execute_C_ADDI16SP. Qed.

  Lemma his_2a : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x2a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc2 (KernelSyms.holding + 0x2a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x2a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) podec_2a exec_execute_C_JR. Qed.

End WpHolding.
