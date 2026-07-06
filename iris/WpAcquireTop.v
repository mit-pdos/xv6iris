(* WpAcquireTop.v -- decode/leaf lemmas for xv6's acquire() in S-mode: one
   [instr] lemma per instruction of acquire() (aqi_00 .. aqi_32) plus the
   underlying decode/execute facts they build on (aqdec_*, aq_cr1, aq_imm16,
   aqexec_sd, aq_addv_zero_l, aq_sextw_round, ...).  These are consumed by
   WpAcquireLock.wp_acquire_lock{_loop}, the CSL acquire spec that supersedes
   the plain-ownership top-level WP formerly proved in this file (see
   WpAcquireLock.v's header for the current top-level story).

   Disassembly (KernelInstrs.v, symbol acquire @ 0x80000bfa):
     +0x00  1101      c.addi   sp,sp,-32
     +0x02  ec06      c.sdsp   ra,24(sp)
     +0x04  e822      c.sdsp   s0,16(sp)
     +0x06  e426      c.sdsp   s1,8(sp)
     +0x08  1000      c.addi4spn s0,sp,32
     +0x0a  84aa      c.mv     s1,a0        s1 := lk
     +0x0c  fbbff0ef  jal      ra,push_off
     +0x10  8526      c.mv     a0,s1
     +0x12  f89ff0ef  jal      ra,holding   (fast path: returns a0 = 0)
     +0x16  4705      c.li     a4,1
     +0x18  ed11      c.bnez   a0,+0x1c     NOT taken (holding returned 0)
     +0x1a  87ba      c.mv     a5,a4
     +0x1c  0cf4a7af  amoswap.w.aq a5,a5,(s1)   (lock word 0 -> 1, a5 := 0)
     +0x20  2781      sext.w   a5
     +0x22  ffe5      c.bnez   a5,-8        NOT taken (old lock word was 0)
     +0x24  4b9000ef  jal      ra,mycpu     a0 := &cpus[cpuid]
     +0x28  e888      c.sd     a0,16(s1)    lk->cpu := a0
     +0x2a  60e2      c.ldsp   ra,24(sp)
     +0x2c  6442      c.ldsp   s0,16(sp)
     +0x2e  64a2      c.ldsp   s1,8(sp)
     +0x30  6105      c.addi16sp sp,32
     +0x32  8082      c.ret                                                  *)
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
Require Import WpPushOffMem WpPushOffCsr WpMycpu WpPushOffTop.
Require Import WpAmo WpAcquireMem WpHolding.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Definition AQ : Z := KernelSyms.acquire.

(* ===================================================================== *)
(* Decode lemmas for the encodings not already covered by WpPushOffTop /  *)
(* WpMycpu / WpHolding / WpAmo.                                           *)
(* ===================================================================== *)
Local Ltac aq_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac aq_close1 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; aq_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

Local Ltac aq_close0 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; aq_ast
  | apply (exec_currentlyEnabled_Zca s HmisaC) ].

(* +0x0a  0x84aa  c.mv s1,a0 *)
Lemma aqdec_mv_s1_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x84aa : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 10)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x10  0x8526  c.mv a0,s1 *)
Lemma aqdec_mv_a0_s1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8526 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 9)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x1a  0x87ba  c.mv a5,a4 *)
Lemma aqdec_mv_a5_a4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x87ba : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 14)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x16  0x4705  c.li a4,1 *)
Lemma aqdec_li_a4_1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4705 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 14)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x18  0xed11  c.bnez a0,+0x1c *)
Lemma aqdec_bnez_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xed11 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 14, Cregidx (mword_of_int 2)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x22  0xffe5  c.bnez a5,-8 *)
Lemma aqdec_bnez_a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xffe5 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 252, Cregidx (mword_of_int 7)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x28  0xe888  c.sd a0,16(s1) *)
Lemma aqdec_sd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe888 : mword 16)) s
  = Some (C_SD (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* ---- base (4-byte) decodes: the three jal's ---- *)
Local Ltac aq_dbase s Hpriv :=
  decode_pause_prefix s Hpriv;
  match goal with |- ?lhs = ?rhs =>
    let l := eval vm_compute in lhs in change_no_check (l = rhs) end;
  aq_ast.

(* +0x0c  0xfbbff0ef  jal ra,push_off (offset -0x46) *)
Lemma aqdec_jal_pushoff s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0xfbbff0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fffba : mword 21, Regidx (mword_of_int 1)), s).
Proof. intro Hpriv. aq_dbase s Hpriv. Qed.

(* +0x12  0xf89ff0ef  jal ra,holding (offset -0x78) *)
Lemma aqdec_jal_holding s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0xf89ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fff88 : mword 21, Regidx (mword_of_int 1)), s).
Proof. intro Hpriv. aq_dbase s Hpriv. Qed.

(* +0x24  0x4b9000ef  jal ra,mycpu (offset +0xcb8) *)
Lemma aqdec_jal_mycpu s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x4b9000ef : mword 32)) s
  = Some (JAL (mword_of_int 0xcb8 : mword 21, Regidx (mword_of_int 1)), s).
Proof. intro Hpriv. aq_dbase s Hpriv. Qed.

(* ---- creg / ExecuteAs expansions ---- *)
Lemma aq_cr1 : creg2reg_idx (Cregidx (mword_of_int 1)) = Regidx (mword_of_int 9).
Proof. vm_compute. reflexivity. Qed.

Lemma aq_imm16 : zero_extend' 12 (concat_vec (mword_of_int 2 : mword 5) ('b"000")) = (mword_of_int 16 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma aqexec_sd s :
  exec (execute (C_SD (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (STORE (mword_of_int 16, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_SD. cbn zeta.
  rewrite exec_returnM. rewrite aq_cr1. rewrite po_cr2. rewrite aq_imm16. reflexivity.
Qed.

(* zero_reg is a left identity for add_vec (mirror of po_addv_assoc's proof) *)
Lemma aq_addv_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite bv_add_unsigned.
  change (bv_unsigned zero_reg) with 0.
  rewrite Z.add_0_l. apply bv_wrap_bv_unsigned.
Qed.

Lemma aq_wrap_signed (n : N) (b : bv n) : bv_wrap n (bv_signed b) = bv_unsigned b.
Proof.
  unfold bv_signed, bv_swrap, bv_wrap.
  rewrite Zminus_mod_idemp_l.
  replace (bv_unsigned b + bv_half_modulus n - bv_half_modulus n) with (bv_unsigned b) by lia.
  apply Z.mod_small. apply bv_unsigned_in_range.
Qed.

Lemma aq_loaded_sext (x : mword 32) : amoswap_loaded x = sign_extend' 64 x.
Proof. unfold amoswap_loaded. f_equal; try (exact (autocast_id 32 x)). Qed.

Lemma aq_subrange_sext (x : mword 32) :
  subrange_vec_dec (sign_extend' 64 x) 31 0 = x.
Proof.
  apply bv_eq.
  unfold subrange_vec_dec.
  unfold to_word_idx, to_word, get_word.
  rewrite MachineWord.cast_idx_refl.
  unfold MachineWord.slice.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.Z_idx 0)) with 0.
  rewrite Z.shiftr_0_r.
  unfold sign_extend', Operators_mwords.sign_extend, Operators_mwords.exts_vec,
    SailStdpp.Values.to_word, to_word, get_word, MachineWord.sign_extend.
  rewrite bv_sign_extend_unsigned.
  rewrite bv_wrap_bv_wrap; [| vm_compute; intro Hc; discriminate Hc].
  apply aq_wrap_signed.
Qed.

Lemma aq_sextw_round (x : mword 32) :
  sign_extend' 64 (subrange_vec_dec (add_vec (amoswap_loaded x)
      (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0)
  = sign_extend' 64 x.
Proof.
  replace (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))) with (mword_of_int 0 : mword 64)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite kv_addv_zero.
  rewrite aq_loaded_sext.
  rewrite aq_subrange_sext.
  reflexivity.
Qed.




Section WpAcquireTop.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

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

  Lemma aqi_00 : kernel_text -∗ instr (mword_of_int (AQ + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc2 (AQ + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (AQ + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) podec_00 exec_execute_C_ADDI. Qed.

  Lemma aqi_02 : kernel_text -∗ instr (mword_of_int (AQ + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc4 (AQ + 0x02)%Z (mword_of_int 0xec06 : mword 16) (mword_of_int 0xe822ec06 : mword 32)
    (mword_of_int (AQ + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) podec_02 exec_execute_C_SDSP. Qed.

  Lemma aqi_04 : kernel_text -∗ instr (mword_of_int (AQ + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc2 (AQ + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (AQ + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) podec_04 exec_execute_C_SDSP. Qed.

  Lemma aqi_06 : kernel_text -∗ instr (mword_of_int (AQ + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc4 (AQ + 0x06)%Z (mword_of_int 0xe426 : mword 16) (mword_of_int 0x1000e426 : mword 32)
    (mword_of_int (AQ + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) podec_06 exec_execute_C_SDSP. Qed.

  Lemma aqi_08 : kernel_text -∗ instr (mword_of_int (AQ + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc2 (AQ + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (AQ + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) podec_08 exec_execute_C_ADDI4SPN. Qed.

  Lemma aqi_0a : kernel_text -∗ instr (mword_of_int (AQ + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc4 (AQ + 0x0a)%Z (mword_of_int 0x84aa : mword 16) (mword_of_int 0xf0ef84aa : mword 32)
    (mword_of_int (AQ + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) aqdec_mv_s1_a0 exec_execute_C_MV. Qed.

  Lemma aqi_0c : kernel_text -∗ instr (mword_of_int (AQ + 0x0c) : mword 64) false (JAL (mword_of_int 0x1fffba : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (AQ + 0x0c)%Z (mword_of_int 0xfbbff0ef : mword 32)
    (mword_of_int (AQ + 0x0c) : mword 64) (JAL (mword_of_int 0x1fffba : mword 21, Regidx (mword_of_int 1))) aqdec_jal_pushoff. Qed.

  Lemma aqi_10 : kernel_text -∗ instr (mword_of_int (AQ + 0x10) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc2 (AQ + 0x10)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (AQ + 0x10) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) aqdec_mv_a0_s1 exec_execute_C_MV. Qed.

  Lemma aqi_12 : kernel_text -∗ instr (mword_of_int (AQ + 0x12) : mword 64) false (JAL (mword_of_int 0x1fff88 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (AQ + 0x12)%Z (mword_of_int 0xf89ff0ef : mword 32)
    (mword_of_int (AQ + 0x12) : mword 64) (JAL (mword_of_int 0x1fff88 : mword 21, Regidx (mword_of_int 1))) aqdec_jal_holding. Qed.

  Lemma aqi_16 : kernel_text -∗ instr (mword_of_int (AQ + 0x16) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc4 (AQ + 0x16)%Z (mword_of_int 0x4705 : mword 16) (mword_of_int 0xed114705 : mword 32)
    (mword_of_int (AQ + 0x16) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) aqdec_li_a4_1 exec_execute_C_LI. Qed.

  Lemma aqi_18 : kernel_text -∗ instr (mword_of_int (AQ + 0x18) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)).
  Proof. mk_rvc2 (AQ + 0x18)%Z (mword_of_int 0xed11 : mword 16)
    (mword_of_int (AQ + 0x18) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)) aqdec_bnez_a0 hexec_bnez. Qed.

  Lemma aqi_1a : kernel_text -∗ instr (mword_of_int (AQ + 0x1a) : mword 64) true (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc4 (AQ + 0x1a)%Z (mword_of_int 0x87ba : mword 16) (mword_of_int 0xa7af87ba : mword 32)
    (mword_of_int (AQ + 0x1a) : mword 64) (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 15), ADD)) aqdec_mv_a5_a4 exec_execute_C_MV. Qed.

  Lemma aqi_1c : kernel_text -∗ instr (mword_of_int (AQ + 0x1c) : mword 64) false amoswap_acq_ast.
  Proof. mk_base (AQ + 0x1c)%Z (mword_of_int 0x0cf4a7af : mword 32)
    (mword_of_int (AQ + 0x1c) : mword 64) amoswap_acq_ast amodec. Qed.

  Lemma aqi_20 : kernel_text -∗ instr (mword_of_int (AQ + 0x20) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc2 (AQ + 0x20)%Z (mword_of_int 0x2781 : mword 16)
    (mword_of_int (AQ + 0x20) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) mydec_addiw exec_execute_C_ADDIW. Qed.

  Lemma aqi_22 : kernel_text -∗ instr (mword_of_int (AQ + 0x22) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc4 (AQ + 0x22)%Z (mword_of_int 0xffe5 : mword 16) (mword_of_int 0x00efffe5 : mword 32)
    (mword_of_int (AQ + 0x22) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) aqdec_bnez_a5 hexec_bnez. Qed.

  Lemma aqi_24 : kernel_text -∗ instr (mword_of_int (AQ + 0x24) : mword 64) false (JAL (mword_of_int 0xcb8 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (AQ + 0x24)%Z (mword_of_int 0x4b9000ef : mword 32)
    (mword_of_int (AQ + 0x24) : mword 64) (JAL (mword_of_int 0xcb8 : mword 21, Regidx (mword_of_int 1))) aqdec_jal_mycpu. Qed.

  Lemma aqi_28 : kernel_text -∗ instr (mword_of_int (AQ + 0x28) : mword 64) true (STORE (mword_of_int 16, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc2 (AQ + 0x28)%Z (mword_of_int 0xe888 : mword 16)
    (mword_of_int (AQ + 0x28) : mword 64) (STORE (mword_of_int 16, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)) aqdec_sd aqexec_sd. Qed.

  Lemma aqi_2a : kernel_text -∗ instr (mword_of_int (AQ + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc4 (AQ + 0x2a)%Z (mword_of_int 0x60e2 : mword 16) (mword_of_int 0x644260e2 : mword 32)
    (mword_of_int (AQ + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) podec_22 exec_execute_C_LDSP. Qed.

  Lemma aqi_2c : kernel_text -∗ instr (mword_of_int (AQ + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc2 (AQ + 0x2c)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (AQ + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) podec_24 exec_execute_C_LDSP. Qed.

  Lemma aqi_2e : kernel_text -∗ instr (mword_of_int (AQ + 0x2e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc4 (AQ + 0x2e)%Z (mword_of_int 0x64a2 : mword 16) (mword_of_int 0x610564a2 : mword 32)
    (mword_of_int (AQ + 0x2e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) podec_26 exec_execute_C_LDSP. Qed.

  Lemma aqi_30 : kernel_text -∗ instr (mword_of_int (AQ + 0x30) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc2 (AQ + 0x30)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (AQ + 0x30) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) podec_28 exec_execute_C_ADDI16SP. Qed.

  Lemma aqi_32 : kernel_text -∗ instr (mword_of_int (AQ + 0x32) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc4 (AQ + 0x32)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int 0x65178082 : mword 32)
    (mword_of_int (AQ + 0x32) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) podec_2a exec_execute_C_JR. Qed.

End WpAcquireTop.
