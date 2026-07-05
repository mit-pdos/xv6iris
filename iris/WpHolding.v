(* WpHolding.v -- whole-function WP for xv6's holding() FAST PATH in S-mode:
   when the spinlock's [locked] word reads 0, holding() is four compressed
   instructions with no stack frame and no mycpu() call:

     holding @ 0x80000b94 (KernelInstrs.kernel_bytes):
       +0x0  411c  c.lw  a5,0(a0)     a5 := sext32(lk->locked)
       +0x2  e399  c.bnez a5,+0x8     NOT taken (locked = 0)
       +0x4  4501  c.li  a0,0         a0 := 0
       +0x6  8082  c.ret              return to ra

   The composition follows WpMycpu.v; the c.bnez fall-through leaf
   [wp_cbnez_fall_s] mirrors WpMemsetS.wp_cbeqz_fall_s_config with BNE. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
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
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode lemmas (podec-style; the tactics mirror WpPushOffTop's).        *)
(* ===================================================================== *)
Local Ltac h_reg_step name w hi lo s :=
  assert (name : exec (encdec_reg_backwards (subrange_vec_dec w hi lo)) s
              = Some (Regidx (autocast (T := mword)
                        (subrange_vec_dec (subrange_vec_dec w hi lo)
                           (Z.sub regidx_bit_width 1) 0)), s));
  [ unfold encdec_reg_backwards;
    match goal with |- context[if ?g then returnM (Regidx _) else _] =>
      replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM
  | idtac ].

Local Ltac h_open_rvc s HmisaC :=
  unfold ext_decode_compressed, encdec_compressed_backwards; cbv beta; cbn zeta;
  skip_pure_clause; repeat (dstep s HmisaC);
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end;
  cbn match; rewrite exec_bind.

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
  intro H. h_open_rvc s H. h_close0 s H.
Qed.

(* +0x2  0xe399  c.bnez a5,+0x8 *)
Lemma hdec_bnez s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe399 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 3, Cregidx (mword_of_int 7)), s).
Proof.
  intro H. h_open_rvc s H. h_close1 s H.
Qed.

(* +0x4  0x4501  c.li a0,0 *)
Lemma hdec_li s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4501 : mword 16)) s
  = Some (C_LI (mword_of_int 0, Regidx (mword_of_int 10)), s).
Proof.
  intro H. h_reg_step Hr (mword_of_int 0x4501 : mword 16) 11 7 s.
  h_open_rvc s H. rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta. h_close1 s H.
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
  intro H. h_open_rvc s H.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; h_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact H ].
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
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
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
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hrs Hrd1 Hcmp)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov ltac:(discriminate) Hpmpp Hpteregion Halignp
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
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
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
    intros tgt HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hrs Hrd1 Hcmp Hal0 Hal1.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov ltac:(discriminate) Hpmpp Hpteregion Halignp
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

  (* =================================================================== *)
  (*  wp_holding_fast: holding() when the lock word reads 0 -- returns    *)
  (*  a0 = 0 to the caller, clobbering only a5 (:= 0-extended lock word). *)
  (* =================================================================== *)
  Lemma wp_holding_fast (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (svpn_lk : mword 27) (lockv : mword 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq dqm : dfrac} :
    let pcE : mword 64 := mword_of_int KernelSyms.holding in
    let a_lk := add_vec (m !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) in
    let m1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 lockv)]> m in
    let m2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> m1 in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (* the lock word's data-slot geometry (R load, 4 bytes) *)
    po_slot_geom root_ppn pmpaddr00 svpn_lk a_lk 4 ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (* fast path: the lock word reads 0 *)
    neq_vec (sign_extend' 64 lockv) zero_reg = false ->
    (* return target alignment *)
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    ([∗ list] j ∈ seq 0 4, (pa_add a_lk j) ↦ₘ{ dqm } nth_byte lockv j) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗ gpr_file m2 -∗
      ([∗ list] j ∈ seq 0 4, (pa_add a_lk j) ↦ₘ{ dqm } nth_byte lockv j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcE a_lk m1 m2 ret_tgt
      HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
      HX Hcov Hpmpp Hpteregion Halignp
      Hslot HR Hlock0 Hal0.
    destruct Hslot as (Lcanon & Lvpn & Lident & Lmask & Lvpn2 & Lmvpn & Lmppn & Lrange & Lalign & Lpalign).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             #Htext Hpc Hfile Hlk Hcont".
    iPoseProof (hi_00 with "Htext") as "Hi00".
    iPoseProof (hi_02 with "Htext") as "Hi02".
    iPoseProof (hi_04 with "Htext") as "Hi04".
    iPoseProof (hi_06 with "Htext") as "Hi06".
    (* +0x0 c.lw a5,0(a0): a5 := sext64 lockv *)
    iApply (wp_clw_s root_ppn E Φ pcE (mword_of_int 15) (mword_of_int 10)
              (mword_of_int 0) svpn_lk m lockv mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              (dq:=dq) (dqm:=dqm)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hcov
              Lcanon Lvpn Lident Lmask Lvpn2 Lmvpn Lmppn Hpmpp Hpteregion Halignp Lrange HR
              Lalign Lpalign
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi00 Hlk [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hlk".
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 lockv)]> m) with m1.
    (* +0x2 c.bnez a5: NOT taken (a5 = sext64 lockv = 0) *)
    assert (Ha5 : m1 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 lockv)
      by (unfold m1; apply lookup_total_insert).
    iApply (wp_cbnez_fall_s root_ppn E Φ (add_vec_int pcE 2) (mword_of_int 3) (Cregidx (mword_of_int 7)) (mword_of_int 15)
              m1 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5; exact Hlock0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi02 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (Hpp4 : add_vec_int (add_vec_int pcE 2) 2 = add_vec_int pcE 4) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4) in "Hpc".
    (* +0x4 c.li a0,0 *)
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ (add_vec_int pcE 4) (mword_of_int 10) (mword_of_int 10) (mword_of_int 10)
              (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI))
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
              m1 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi04 [-]").
    { intros s_pc Hnpc _ _.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) (mword_of_int 10) (sign_extend' 12 (mword_of_int 0 : mword 6)) s_pc).
      replace (Z.eqb (uint (mword_of_int 10 : mword 5)) 0) with false by (vm_compute; reflexivity).
      unfold gpr_addi_val.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true by (vm_compute; reflexivity).
      reflexivity. }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> m1) with m2.
    assert (Hpp6 : add_vec_int (add_vec_int pcE 4) 2 = add_vec_int pcE 6) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6) in "Hpc".
    (* +0x6 c.ret *)
    assert (Hra2 : m2 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { unfold m2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m1. rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate]. }
    iApply (wp_cret_s_zca root_ppn E Φ (add_vec_int pcE 6) (mword_of_int 1) m2
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate) Hlpe
              ltac:(rewrite Hra2; exact Hal0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi06 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    iEval (rewrite Hra2) in "Hpc".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hlk").
  Qed.

  (* =================================================================== *)
  (*  wp_holding: holding() for an ARBITRARY lock word, provided the      *)
  (*  lock is not already held by this cpu (lk->cpu <> &cpus[cpuid]) --   *)
  (*  so holding() returns a0 = 0 on BOTH paths and acquire() does not    *)
  (*  panic.  Fast path (lock word 0): 4 instructions, no memory beyond   *)
  (*  the lock word.  Slow path (lock word nonzero): full frame, reads    *)
  (*  lk->cpu, calls mycpu(), compares.  The postcondition tracks         *)
  (*  ra/s0/s1/sp/tp (restored) and a0 = 0; a5/a4 are clobbered; the      *)
  (*  five below-sp scratch cells come back with unspecified contents.    *)
  (* =================================================================== *)
  Lemma wp_holding (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (svpn_lk svpn_cpu : mword 27)
      (lockv : mword 32) (cpuold : mword 64)
      (vp24 vp16 vp8 vfra vfs0 : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dqm dqc : dfrac} :
    let pcE : mword 64 := mword_of_int KernelSyms.holding in
    let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
    let a_lk := add_vec lk (sign_extend' 64 (mword_of_int 0 : mword 12)) in
    let a_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    let spdh := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let a_h24 := add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_h16 := add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_h8  := add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let mc_sp := add_vec spdh (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let a_fra := add_vec mc_sp (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a_fs0 := add_vec mc_sp (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    (* fetch geometry over holding's whole body: a single X-bit fact, threaded
       to every instruction; the RAM/PMP geometry is derived from instr_bytes *)
    po_mycpu_geom pmpcfg0 pmpaddr00 ->
    (* data-slot geometry *)
    po_slot_geom root_ppn pmpaddr00 svpn_lk a_lk 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_cpu a_cpu 8 ->
    po_slot_align a_h24 8 -> po_slot_align a_h16 8 -> po_slot_align a_h8 8 ->
    po_slot_align a_fra 8 -> po_slot_align a_fs0 8 ->
    (* the lock is not held by THIS cpu *)
    eq_vec cpuold (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) = false ->
    (* return target alignment *)
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    ([∗ list] j ∈ seq 0 4, (pa_add a_lk j) ↦ₘ{ dqm } nth_byte lockv j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_cpu j) ↦ₘ{ dqc } nth_byte cpuold j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_h24 j) ↦ₘ nth_byte vp24 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_h16 j) ↦ₘ nth_byte vp16 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_h8 j) ↦ₘ nth_byte vp8 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_fra j) ↦ₘ nth_byte vfra j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_fs0 j) ↦ₘ nth_byte vfs0 j) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
      mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      (∃ mh, gpr_file mh ∗
        ⌜ mh !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5) /\
          mh !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5) /\
          mh !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5) /\
          mh !!! Regidx csp_rs1 = m !!! Regidx csp_rs1 /\
          mh !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5) /\
          mh !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64) ⌝) -∗
      ([∗ list] j ∈ seq 0 4, (pa_add a_lk j) ↦ₘ{ dqm } nth_byte lockv j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add a_cpu j) ↦ₘ{ dqc } nth_byte cpuold j) -∗
      (∃ (w24 w16 w8 wra ws0 : bv 64),
        ([∗ list] j ∈ seq 0 8, (pa_add a_h24 j) ↦ₘ nth_byte w24 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add a_h16 j) ↦ₘ nth_byte w16 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add a_h8 j) ↦ₘ nth_byte w8 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add a_fra j) ↦ₘ nth_byte wra j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add a_fs0 j) ↦ₘ nth_byte ws0 j)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcE lk a_lk a_cpu spdh a_h24 a_h16 a_h8 mc_sp a_fra a_fs0 ret_tgt
      HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hpmpp Hpteregion Halignp HW HR Hramcov
      Hmyg Hg_lk Hg_cpu Hg_h24 Hg_h16 Hg_h8 Hg_fra Hg_fs0 Hnotmine Hal0.
    pose proof Hg_lk as (Lcanon & Lvpn & Lident & Lmask & Lvpn2 & Lmvpn & Lmppn & Lrange & Lalign & Lpalign).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             #Htext Hpc Hfile Hlk Hcpu Hh24 Hh16 Hh8 Hfra Hfs0 Hcont".
    iPoseProof (hi_00 with "Htext") as "Hi00".
    iPoseProof (hi_02 with "Htext") as "Hi02".
    (* +0x0 c.lw a5,0(a0): a5 := sext64 lockv *)
    iApply (wp_clw_s root_ppn E Φ pcE (mword_of_int 15) (mword_of_int 10)
              (mword_of_int 0) svpn_lk m lockv mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              (dq:=DfracOwn 1) (dqm:=dqm)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Lcanon Lvpn Lident Lmask Lvpn2 Lmvpn Lmppn Hpmpp Hpteregion Halignp Lrange HR
              Lalign Lpalign
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi00 Hlk [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hlk".
    set (H1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 lockv)]> m).
    assert (Ha5 : H1 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 lockv)
      by (rewrite /H1; apply lookup_total_insert).
    assert (Hpp2 : add_vec_int pcE 2 = mword_of_int (KernelSyms.holding + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2) in "Hpc".
    (* case split: is the lock held? *)
    destruct (neq_vec (sign_extend' 64 lockv) zero_reg) eqn:Hheld.
    - (* ===== SLOW PATH: lock word nonzero, c.bnez TAKEN ===== *)
      iApply (wp_cbnez_taken_s root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x02)) (mword_of_int 3) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                H1 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5; exact Hheld)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi02 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      assert (Hpc08 : add_vec (mword_of_int (KernelSyms.holding + 0x02) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                      = mword_of_int (KernelSyms.holding + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc08) in "Hpc".
      iPoseProof (his_08 with "Htext") as "Hi08".
      iPoseProof (his_0a with "Htext") as "Hi0a".
      iPoseProof (his_0c with "Htext") as "Hi0c".
      iPoseProof (his_0e with "Htext") as "Hi0e".
      iPoseProof (his_10 with "Htext") as "Hi10".
      iPoseProof (his_12 with "Htext") as "Hi12".
      iPoseProof (his_14 with "Htext") as "Hi14".
      iPoseProof (his_16 with "Htext") as "Hi16".
      iPoseProof (his_1a with "Htext") as "Hi1a".
      iPoseProof (his_1e with "Htext") as "Hi1e".
      iPoseProof (his_22 with "Htext") as "Hi22".
      iPoseProof (his_24 with "Htext") as "Hi24".
      iPoseProof (his_26 with "Htext") as "Hi26".
      iPoseProof (his_28 with "Htext") as "Hi28".
      iPoseProof (his_2a with "Htext") as "Hi2a".
      pose proof Hg_h24 as [A24 P24]. pose proof Hg_h16 as [A16 P16]. pose proof Hg_h8 as [A8 P8].
      (* +0x08 c.addi sp,-32 *)
      iApply (wp_caddi_gpr_s_config root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x08)) csp_rs1 (mword_of_int 32 : mword 6) H1
                mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi08 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      set (H2 := <[Regidx csp_rs1 := regval_into_reg (add_vec (H1 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> H1).
      assert (HspH1 : H1 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
        by (rewrite /H1; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
      assert (HspH2 : H2 !!! Regidx csp_rs1 = spdh)
        by (rewrite /H2; rewrite lookup_total_insert; rewrite HspH1; reflexivity).
      assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.holding + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp0a) in "Hpc".
      (* +0x0a c.sdsp ra,24(sp) *)
      iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x0a)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                H2 vp24 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
                Hpmpp Hpteregion Halignp Hramcov HW
                ltac:(rewrite HspH2; exact A24) ltac:(rewrite HspH2; exact P24)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0a [Hh24] [-]").
      { iEval (rewrite HspH2). iExact "Hh24". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hh24".
      assert (HraH2 : H2 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HspH2 HraH2) in "Hh24".
      assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.holding + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp0c) in "Hpc".
      (* +0x0c c.sdsp s0,16(sp) *)
      iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x0c)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                H2 vp16 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
                Hpmpp Hpteregion Halignp Hramcov HW
                ltac:(rewrite HspH2; exact A16) ltac:(rewrite HspH2; exact P16)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0c [Hh16] [-]").
      { iEval (rewrite HspH2). iExact "Hh16". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hh16".
      assert (Hs0H2 : H2 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
      { rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HspH2 Hs0H2) in "Hh16".
      assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.holding + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp0e) in "Hpc".
      (* +0x0e c.sdsp s1,8(sp) *)
      iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x0e)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                H2 vp8 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
                Hpmpp Hpteregion Halignp Hramcov HW
                ltac:(rewrite HspH2; exact A8) ltac:(rewrite HspH2; exact P8)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0e [Hh8] [-]").
      { iEval (rewrite HspH2). iExact "Hh8". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hh8".
      assert (Hs1H2 : H2 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
      { rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HspH2 Hs1H2) in "Hh8".
      assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.holding + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp10) in "Hpc".
      (* +0x10 c.addi4spn s0,sp,32 *)
      iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x10)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
                H2 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi10 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      set (H3 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (H2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> H2).
      assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.holding + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp12) in "Hpc".
      (* +0x12 c.ld a5,16(a0): a5 := lk->cpu *)
      assert (Ha0H3 : H3 !!! Regidx (mword_of_int 10 : mword 5) = lk).
      { rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      assert (HAcpu : add_vec (H3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = a_cpu)
        by (rewrite Ha0H3; reflexivity).
      pose proof Hg_cpu as (Ccanon & Cvpn & Cident & Cmask & Cvpn2 & Cmvpn & Cmppn & Crange & Calign & Cpalign).
      iApply (wp_cld_s root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x12)) (mword_of_int 15) (mword_of_int 10)
                (mword_of_int 16) svpn_cpu H3 cpuold mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
                (dq:=DfracOwn 1) (dqm:=dqc)
                HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
                ltac:(rewrite HAcpu; exact Ccanon) ltac:(rewrite HAcpu; exact Cvpn) ltac:(rewrite HAcpu; exact Cident)
                Cmask Cvpn2 Cmvpn Cmppn Hpmpp Hpteregion Halignp ltac:(rewrite HAcpu; exact Crange) HR
                ltac:(rewrite HAcpu; exact Calign) ltac:(rewrite HAcpu; exact Cpalign)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi12 [Hcpu] [-]").
      { iEval (rewrite HAcpu). iExact "Hcpu". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hcpu".
      iEval (rewrite HAcpu) in "Hcpu".
      set (H4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg cpuold]> H3).
      assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.holding + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp14) in "Hpc".
      (* +0x14 c.mv s1,a5 *)
      iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x14)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5)
                H4 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi14 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      set (H5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (H4 !!! Regidx (mword_of_int 15 : mword 5)))]> H4).
      assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.holding + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp16) in "Hpc".
      (* +0x16 jal ra,mycpu; the whole mycpu() *)
      assert (HspH5 : H5 !!! Regidx csp_rs1 = spdh).
      { rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HspH2. }
      assert (HspH6 : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.holding + 0x16) : mword 64) 4)]> H5) !!! Regidx csp_rs1 = spdh)
        by (rewrite lookup_total_insert_ne; [ exact HspH5 | vm_compute; discriminate ]).
      pose proof Hg_fra as [FRAa FRAp]. pose proof Hg_fs0 as [FS0a FS0p].
      assert (EQ18 : add_vec_int (mword_of_int (KernelSyms.holding + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_pushoff_call_mycpu root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x16)) (mword_of_int 0xd2c : mword 21) H5 vfra vfs0
                mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
                HN ltac:(apply bv_eq; vm_compute; reflexivity) Hmyg
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
                Hpmpp Hpteregion Halignp
                ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
                HW HR Hramcov
                ltac:(rewrite HspH6; exact (conj FRAa FRAp))
                ltac:(rewrite HspH6; exact (conj FS0a FS0p))
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile Hi16 [Hfra] [Hfs0] [-]").
      { iEval (rewrite HspH6). iExact "Hfra". }
      { iEval (rewrite HspH6). iExact "Hfs0". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hfra Hfs0".
      iEval (rewrite HspH6) in "Hfra". iEval (rewrite HspH6) in "Hfs0".
      iEval (rewrite lookup_total_insert) in "Hpc".
      assert (Hpc1a : update_vec_dec (add_vec (add_vec_int (mword_of_int (KernelSyms.holding + 0x16) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                      = (mword_of_int (KernelSyms.holding + 0x1a) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc1a) in "Hpc".
      set (C := po_mycpu_out (mword_of_int (KernelSyms.holding + 0x16)) H5).
      (* +0x1a sub a0,s1,a0 *)
      assert (Hs1C : C !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg cpuold).
      { rewrite /C po_mycpu_out_s1. rewrite /H5. rewrite lookup_total_insert.
        rewrite /H4. rewrite lookup_total_insert. reflexivity. }
      assert (Ha0C : C !!! Regidx (mword_of_int 10 : mword 5) = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))).
      { rewrite /C po_mycpu_out_a0.
        rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      unshelve iApply (wp_gpr_write_s_config_base_pc root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x1a)) (mword_of_int 10) (mword_of_int 9) (mword_of_int 10)
                (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 9), Regidx (mword_of_int 10), SUB))
                (sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5)))
                C mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov
                ltac:(vm_compute; reflexivity)
                Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
                _
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1a [-]").
      { intros s_pc Hnpc Hpcv Hva Hvb.
        change (execute (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 9), Regidx (mword_of_int 10), SUB)))
          with (execute_RTYPE (Regidx (mword_of_int 10)) (Regidx (mword_of_int 9)) (Regidx (mword_of_int 10)) SUB).
        rewrite (exec_execute_RTYPE_SUB_gpr (mword_of_int 10) (mword_of_int 9) (mword_of_int 10) s_pc).
        replace (Z.eqb (uint (mword_of_int 10 : mword 5)) 0) with false by (vm_compute; reflexivity).
        unfold gpr_sub_val. rewrite Hva Hvb. reflexivity. }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      set (H6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5)))]> C).
      assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.holding + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.holding + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      (* +0x1e seqz a0,a0 *)
      assert (Ha0H6 : H6 !!! Regidx (mword_of_int 10 : mword 5)
                      = sub_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (C !!! Regidx (mword_of_int 10 : mword 5)))
        by (rewrite /H6; apply lookup_total_insert).
      unshelve iApply (wp_gpr_write_s_config_base_pc root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x1e)) (mword_of_int 10) (mword_of_int 10) (mword_of_int 10)
                (ITYPE (mword_of_int 1, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLTIU))
                (zero_extend' 64 (bool_to_bit (zopz0zI_u (H6 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))))
                H6 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov
                ltac:(vm_compute; reflexivity)
                Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
                _
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1e [-]").
      { intros s_pc Hnpc Hpcv Hva Hvb.
        rewrite (exec_execute_ITYPE_SLTIU_gpr (mword_of_int 10) (mword_of_int 10) (mword_of_int 1) s_pc).
        replace (Z.eqb (uint (mword_of_int 10 : mword 5)) 0) with false by (vm_compute; reflexivity).
        unfold gpr_sltiu_val. rewrite Hva. reflexivity. }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      set (H7 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (zero_extend' 64 (bool_to_bit (zopz0zI_u (H6 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))))]> H6).
      assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.holding + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.holding + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 c.ldsp ra,24(sp) *)
      assert (HspC : C !!! Regidx csp_rs1 = spdh).
      { rewrite /C po_mycpu_out_csp. exact HspH5. }
      assert (HspH7 : H7 !!! Regidx csp_rs1 = spdh).
      { rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HspC. }
      iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x22)) (mword_of_int 3) (mword_of_int 1 : mword 5)
                H7 (m !!! Regidx (mword_of_int 1 : mword 5))
                mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
                Hpmpp Hpteregion Halignp Hramcov HR
                ltac:(rewrite HspH7; exact A24) ltac:(rewrite HspH7; exact P24)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi22 [Hh24]").
      { iEval (rewrite HspH7). iExact "Hh24". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hh24".
      iEval (rewrite HspH7) in "Hh24".
      set (H8 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> H7).
      assert (HspH8 : H8 !!! Regidx csp_rs1 = spdh)
        by (rewrite /H8; rewrite lookup_total_insert_ne; [ exact HspH7 | vm_compute; discriminate ]).
      assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.holding + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      (* +0x24 c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x24)) (mword_of_int 2) (mword_of_int 8 : mword 5)
                H8 (m !!! Regidx (mword_of_int 8 : mword 5))
                mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
                Hpmpp Hpteregion Halignp Hramcov HR
                ltac:(rewrite HspH8; exact A16) ltac:(rewrite HspH8; exact P16)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi24 [Hh16]").
      { iEval (rewrite HspH8). iExact "Hh16". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hh16".
      iEval (rewrite HspH8) in "Hh16".
      set (H9 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> H8).
      assert (HspH9 : H9 !!! Regidx csp_rs1 = spdh)
        by (rewrite /H9; rewrite lookup_total_insert_ne; [ exact HspH8 | vm_compute; discriminate ]).
      assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.holding + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* +0x26 c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x26)) (mword_of_int 1) (mword_of_int 9 : mword 5)
                H9 (m !!! Regidx (mword_of_int 9 : mword 5))
                mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
                Hpmpp Hpteregion Halignp Hramcov HR
                ltac:(rewrite HspH9; exact A8) ltac:(rewrite HspH9; exact P8)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi26 [Hh8]").
      { iEval (rewrite HspH9). iExact "Hh8". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hh8".
      iEval (rewrite HspH9) in "Hh8".
      set (H10 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> H9).
      assert (HspH10 : H10 !!! Regidx csp_rs1 = spdh)
        by (rewrite /H10; rewrite lookup_total_insert_ne; [ exact HspH9 | vm_compute; discriminate ]).
      assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.holding + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp28) in "Hpc".
      (* +0x28 c.addi16sp sp,32 *)
      iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                   with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
        as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
      iApply (wp_caddi16sp_gpr_s root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x28)) (mword_of_int 2 : mword 6) H10
                pmpcfg0 pmpaddr00 region_pte (1/2)%Qp HN Hmyg Hramcov Hpmpp Hpteregion Halignp
                with "Hsm Hpca Hpaa Htlbinv Hpc Hfile Hi28 [-]").
      iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
      iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                   with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
        as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
      set (H11 := <[Regidx csp_rs1 := regval_into_reg (add_vec (H10 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> H10).
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.holding + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      (* +0x2a c.ret *)
      assert (HraH11 : H11 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H8. apply lookup_total_insert. }
      iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x2a)) (mword_of_int 1) H11
                mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate) Hlpe
                ltac:(rewrite HraH11; exact Hal0)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2a [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      iEval (rewrite HraH11) in "Hpc".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc [Hfile] Hlk Hcpu [Hh24 Hh16 Hh8 Hfra Hfs0]").
      { iExists H11. iFrame "Hfile". iPureIntro.
        split; [exact HraH11|]. split; [|split; [|split; [|split]]].
        - rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. apply lookup_total_insert.
        - rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. apply lookup_total_insert.
        - rewrite /H11. rewrite lookup_total_insert. rewrite HspH10.
          rewrite /spdh po_addv_assoc.
          replace (add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                           (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))
            with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
          apply kv_addv_zero.
        - rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_tp.
          rewrite /H5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - rewrite /H11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H7. rewrite lookup_total_insert.
          rewrite Ha0H6 Hs1C Ha0C.
          rewrite add_vec_zero_l.
          apply seqz_sub_neq. exact Hnotmine.
      }
      iExists _, _, _, _, _. iFrame "Hh24 Hh16 Hh8 Hfra Hfs0".
    - (* ===== FAST PATH: lock word 0, c.bnez NOT taken ===== *)
      iApply (wp_cbnez_fall_s root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x02)) (mword_of_int 3) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                H1 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5; exact Hheld)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi02 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.holding + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp04) in "Hpc".
      (* +0x04 c.li a0,0 *)
      iPoseProof (hi_04 with "Htext") as "Hi04".
      unshelve iApply (wp_gpr_write_s_config root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x04)) (mword_of_int 10) (mword_of_int 10) (mword_of_int 10)
                (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI))
                (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
                H1 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
                _
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi04 [-]").
      { intros s_pc Hnpc _ _.
        change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
        rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) (mword_of_int 10) (sign_extend' 12 (mword_of_int 0 : mword 6)) s_pc).
        replace (Z.eqb (uint (mword_of_int 10 : mword 5)) 0) with false by (vm_compute; reflexivity).
        unfold gpr_addi_val.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true by (vm_compute; reflexivity).
        reflexivity. }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      set (H2f := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> H1).
      assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.holding + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.holding + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp06) in "Hpc".
      (* +0x06 c.ret *)
      iPoseProof (hi_06 with "Htext") as "Hi06".
      assert (HraH2f : H2f !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /H2f. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (KernelSyms.holding + 0x06)) (mword_of_int 1) H2f
                mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate) Hlpe
                ltac:(rewrite HraH2f; exact Hal0)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi06 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      iEval (rewrite HraH2f) in "Hpc".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc [Hfile] Hlk Hcpu [Hh24 Hh16 Hh8 Hfra Hfs0]").
      { iExists H2f. iFrame "Hfile". iPureIntro.
        split; [exact HraH2f|]. split; [|split; [|split; [|split]]].
        - rewrite /H2f. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - rewrite /H2f. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - rewrite /H2f. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - rewrite /H2f. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /H1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - rewrite /H2f. rewrite lookup_total_insert. apply bv_eq. vm_compute. reflexivity.
      }
      iExists vp24, vp16, vp8, vfra, vfs0. iFrame "Hh24 Hh16 Hh8 Hfra Hfs0".
  Qed.

End WpHolding.
