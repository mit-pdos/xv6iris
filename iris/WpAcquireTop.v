(* WpAcquireTop.v -- the top-level WP for xv6's acquire() in S-mode, for an
   ARBITRARY initial lock word (held or free), provided the lock is not
   already held by THIS cpu (so holding() returns 0 and acquire() does not
   panic).  If the lock word is 0 the amoswap test-and-set succeeds on the
   first iteration and acquire() returns with the postcondition below; if it
   is nonzero the amoswap writes 1 and loops -- in this single-hart model
   nothing ever releases the lock, so the loop spins forever, which is
   proved by Löb induction ([wp_acquire_spin], cf. WpSpinNew.wp_spin).
   Composes: the prologue/epilogue stack ops, the three calls
   (wp_push_off / wp_holding / wp_mycpu), the amoswap.w.aq leaf
   (wp_amoswap_w_s), the c.bnez branches (both arms), and the final
   [sd a0,16(s1)] (wp_csd_s) recording lk->cpu = &cpus[cpuid].

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
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Definition AQ : Z := KernelSyms.acquire.

(* ===================================================================== *)
(* Decode lemmas for the encodings not already covered by WpPushOffTop /  *)
(* WpMycpu / WpHolding / WpAmo.                                           *)
(* ===================================================================== *)
Local Ltac aq_reg_step name w hi lo s :=
  assert (name : exec (encdec_reg_backwards (subrange_vec_dec w hi lo)) s
              = Some (Regidx (autocast (T := mword)
                        (subrange_vec_dec (subrange_vec_dec w hi lo)
                           (Z.sub regidx_bit_width 1) 0)), s));
  [ unfold encdec_reg_backwards;
    match goal with |- context[if ?g then returnM (Regidx _) else _] =>
      replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM
  | idtac ].

Local Ltac aq_open_rvc s HmisaC :=
  unfold ext_decode_compressed, encdec_compressed_backwards; cbv beta; cbn zeta;
  skip_pure_clause; cwalk s HmisaC;
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end;
  cbn match; rewrite exec_bind.

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
  intro H. aq_reg_step Hr1 (mword_of_int 0x84aa : mword 16) 11 7 s.
  aq_reg_step Hr2 (mword_of_int 0x84aa : mword 16) 6 2 s.
  aq_open_rvc s H.
  rewrite (exec_bind_Some _ _ _ _ _ Hr1). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hr2). cbn beta.
  aq_close1 s H.
Qed.

(* +0x10  0x8526  c.mv a0,s1 *)
Lemma aqdec_mv_a0_s1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8526 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 9)), s).
Proof.
  intro H. aq_reg_step Hr1 (mword_of_int 0x8526 : mword 16) 11 7 s.
  aq_reg_step Hr2 (mword_of_int 0x8526 : mword 16) 6 2 s.
  aq_open_rvc s H.
  rewrite (exec_bind_Some _ _ _ _ _ Hr1). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hr2). cbn beta.
  aq_close1 s H.
Qed.

(* +0x1a  0x87ba  c.mv a5,a4 *)
Lemma aqdec_mv_a5_a4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x87ba : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 14)), s).
Proof.
  intro H. aq_reg_step Hr1 (mword_of_int 0x87ba : mword 16) 11 7 s.
  aq_reg_step Hr2 (mword_of_int 0x87ba : mword 16) 6 2 s.
  aq_open_rvc s H.
  rewrite (exec_bind_Some _ _ _ _ _ Hr1). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hr2). cbn beta.
  aq_close1 s H.
Qed.

(* +0x16  0x4705  c.li a4,1 *)
Lemma aqdec_li_a4_1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4705 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 14)), s).
Proof.
  intro H. aq_reg_step Hr (mword_of_int 0x4705 : mword 16) 11 7 s.
  aq_open_rvc s H. rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta. aq_close1 s H.
Qed.

(* +0x18  0xed11  c.bnez a0,+0x1c *)
Lemma aqdec_bnez_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xed11 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 14, Cregidx (mword_of_int 2)), s).
Proof.
  intro H. aq_open_rvc s H. aq_close1 s H.
Qed.

(* +0x22  0xffe5  c.bnez a5,-8 *)
Lemma aqdec_bnez_a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xffe5 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 252, Cregidx (mword_of_int 7)), s).
Proof.
  intro H. aq_open_rvc s H. aq_close1 s H.
Qed.

(* +0x28  0xe888  c.sd a0,16(s1) *)
Lemma aqdec_sd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe888 : mword 16)) s
  = Some (C_SD (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)), s).
Proof.
  intro H. aq_open_rvc s H. aq_close0 s H.
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


  Notation PO := KernelSyms.push_off.

  (* =================================================================== *)
  (*  wp_acquire_spin: once the lock word is 1 and someone else holds it, *)
  (*  acquire()'s test-and-set loop                                       *)
  (*      +0x1a c.mv a5,a4 / +0x1c amoswap / +0x20 sext.w / +0x22 c.bnez  *)
  (*  spins forever: every iteration reads 1, writes 1 back, and branches *)
  (*  to the head.  Proved by Löb induction (cf. WpSpinNew.wp_spin), with *)
  (*  the IH generalized over the (changing) a5 value; the final c.bnez   *)
  (*  step runs on the raw engine so its ▷ strips the IH's later.         *)
  (* =================================================================== *)
  Lemma wp_acquire_spin (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (M0 : gmap regidx (mword 64)) (a5v lk : mword 64) (svpn_lk : mword 27)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) :
    let a4one : mword 64 := add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (* fetch geometry over the loop body: a single X-bit fact + RAM coverage;
       the RAM/PMP fetch geometry is derived internally from instr_bytes *)
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    (* the lock word's data-slot geometry *)
    po_slot_geom root_ppn pmpaddr00 svpn_lk lk 4 ->
    (forall pmar0, pma_allows_all pmar0 ->
       exists region_amo,
         matching_pma_region pmar0 (Physaddr lk) 4 = Some region_amo /\
         (override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_readable) = true /\
         (override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_writable) = true /\
         pma_allows_atomic_op
           ((override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_atomic_support))
           AMOSWAP 4 = true) ->
    (* the loop-invariant register facts *)
    M0 !!! Regidx (mword_of_int 14 : mword 5) = a4one ->
    M0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int (AQ + 0x1a)) -∗
    gpr_file (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg a5v]> M0) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add lk j) ↦ₘ nth_byte (mword_of_int 1 : mword 32) j) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros a4one HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hpmpp Hpteregion Halignp HR HW
      HX Hcov Hg_lk Hpma_amo HM0a4 HM0s1.
    pose proof Hg_lk as (Lcanon & Lvpn & Lident & Lmask & Lvpn2 & Lmvpn & Lmppn & Lrange & Lalign & Lpalign).
    (* a5v-independent register/address facts, posed once outside the Löb *)
    assert (Ha4any : forall w : mword 64,
        (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w]> M0) !!! Regidx (mword_of_int 14 : mword 5) = a4one).
    { intro w. rewrite lookup_total_insert_ne; [ exact HM0a4 | vm_compute; discriminate ]. }
    assert (Hs1any : forall w : mword 64,
        (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w]> M0) !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { intro w. rewrite lookup_total_insert_ne; [ exact HM0s1 | vm_compute; discriminate ]. }
    assert (HAlk2 : add_vec (add_vec zero_reg lk) (zeros' 64) = lk).
    { rewrite aq_addv_zero_l.
      replace (zeros' 64 : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    set (v1 := add_vec zero_reg a4one).
    assert (Hst1 : amoswap_stored v1 = (mword_of_int 1 : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    set (v3 := sign_extend' 64 (subrange_vec_dec
        (add_vec (amoswap_loaded (mword_of_int 1)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0)).
    assert (Hv3nz : neq_vec v3 zero_reg = true) by (vm_compute; reflexivity).
    assert (Htgt : add_vec (mword_of_int (AQ + 0x22) : mword 64)
              (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
            = mword_of_int (AQ + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv #Htext Hpc Hfile Hlock".
    iPoseProof (aqi_1a with "Htext") as "#Hj1a".
    iPoseProof (aqi_1c with "Htext") as "#Hj1c".
    iPoseProof (aqi_20 with "Htext") as "#Hj20".
    iPoseProof (aqi_22 with "Htext") as "#Hj22".
    iRevert "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hlock".
    iLöb as "IH" forall (a5v).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hlock".
    (* ---- +0x1a: c.mv a5,a4 ---- *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (AQ + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg a5v]> M0)
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hj1a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    iEval (rewrite (Ha4any a5v) insert_insert) in "Hfile".
    assert (Hpp1c : add_vec_int (mword_of_int (AQ + 0x1a) : mword 64) 2 = mword_of_int (AQ + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* ---- +0x1c: amoswap.w.aq a5,a5,(s1): reads 1, writes 1 ---- *)
    iApply (wp_amoswap_w_s root_ppn E Φ (mword_of_int (AQ + 0x1c)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 9)
              svpn_lk (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v1]> M0) (mword_of_int 1)
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX
              Hcov
              ltac:(rewrite (Hs1any v1) HAlk2; exact Lcanon)
              ltac:(rewrite (Hs1any v1) HAlk2; exact Lvpn)
              ltac:(rewrite (Hs1any v1) HAlk2; exact Lident)
              Lmask Lvpn2 Lmvpn Lmppn Hpmpp Hpteregion Halignp
              ltac:(rewrite (Hs1any v1) HAlk2; exact Lrange) HR HW
              ltac:(rewrite (Hs1any v1) HAlk2; exact Hpma_amo)
              ltac:(rewrite (Hs1any v1) HAlk2; exact Lalign)
              ltac:(rewrite (Hs1any v1) HAlk2; exact Lpalign)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hj1c [Hlock] [-]").
    { iEval (rewrite (Hs1any v1) HAlk2). iExact "Hlock". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hlock".
    iEval (rewrite (Hs1any v1) HAlk2) in "Hlock".
    iEval (rewrite lookup_total_insert Hst1) in "Hlock".
    iEval (rewrite insert_insert) in "Hfile".
    assert (Hpp20 : add_vec_int (mword_of_int (AQ + 0x1c) : mword 64) 4 = mword_of_int (AQ + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* ---- +0x20: sext.w a5 ---- *)
    iApply (wp_caddiw_s root_ppn E Φ (mword_of_int (AQ + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (amoswap_loaded (mword_of_int 1))]> M0)
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hj20 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    iEval (rewrite lookup_total_insert insert_insert) in "Hfile".
    assert (Hpp22 : add_vec_int (mword_of_int (AQ + 0x20) : mword 64) 2 = mword_of_int (AQ + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* ---- +0x22: c.bnez a5 TAKEN (a5 = sext32(1) <> 0), back to +0x1a ----
       Run on the raw engine so the step's later strips the Löb IH's. *)
    iDestruct "Hpc" as "[Hpc Hnpc]".
    iDestruct "Hfile" as "[%Hdom Hfmap]".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ (mword_of_int (AQ + 0x22)) true
              (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hj22").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v3]> M0) !! Regidx (mword_of_int 15 : mword 5)
                  = Some ((<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v3]> M0) !!! Regidx (mword_of_int 15 : mword 5)))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int (mword_of_int (AQ + 0x22)) 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int (mword_of_int (AQ + 0x22)) 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = mword_of_int (AQ + 0x22)).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value (mword_of_int 15) _ s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iMod (reg_update _ nextPC _ (mword_of_int (AQ + 0x1a)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro. iExists (set_reg s_pc nextPC (mword_of_int (AQ + 0x1a))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc.
      replace (creg2reg_idx (Cregidx (mword_of_int 7))) with (Regidx (mword_of_int 15 : mword 5))
        by (vm_compute; reflexivity).
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : neq_vec (rvv (mword_of_int 15) s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match.
        rewrite lookup_total_insert. exact Hv3nz. }
      epose proof (exec_execute_BTYPE_BNE_taken (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")))
                     (zero_extend' 5 ('b"00")) (mword_of_int 15) s_pc Htk) as Hred.
      rewrite Hpcv Htgt in Hred.
      exact (Hred ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc nextPC (mword_of_int (AQ + 0x1a))).(sregs) = mword_of_int (AQ + 0x1a))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    (* strip the step's later against the Löb hypothesis and loop *)
    iNext.
    iApply ("IH" $! v3 with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes] [$Hpc' $Hnpc] [Hfmap] Hlock").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.



  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the entire acquire(), entry (0x80000bfa)     *)
  (*  through the return to the caller (lock free) or the forever-spin    *)
  (*  (lock held; the continuation below is then simply never invoked).   *)
  (*  Registers: ra=x1 sp=x2 tp=x4 s0=x8 s1=x9 a0=x10 a4=x14 a5=x15.      *)
  (*  On exit: the lock word is 1, lk->cpu = &cpus[cpuid], noff is        *)
  (*  incremented (and intena updated) by push_off, SIE is clear          *)
  (*  (mstatus0's SIE was already required clear), callee-saved           *)
  (*  ra/s0/s1/sp are restored, and a0 = &cpus[cpuid].                    *)
  (* =================================================================== *)
  Lemma wp_acquire (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64))
      (svpn_noff svpn_intena svpn_lk svpn_cpu : mword 27)
      (vr24 vr16 vr8 pr24 pr16 pr8 fraold fs0old cpuold : bv 64)
      (noff intena_old lockv : mword 32) (a0f : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) :
    let AQw : mword 64 := mword_of_int AQ in
    let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    (* acquire's own frame slots (ra/s0/s1 saves at spd+24/+16/+8) *)
    let a_r24 := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_r16 := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_r8  := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    (* push_off's frame below (its sp is spd): slots at spd-8/-16/-24 *)
    let po_spd := add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let a_p24 := add_vec po_spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_p16 := add_vec po_spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_p8  := add_vec po_spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    (* mycpu's frame under push_off: slots at spd-40/-48 *)
    let po_spm10 := add_vec po_spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let a_fra := add_vec po_spm10 (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a_fs0 := add_vec po_spm10 (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    (* the per-cpu noff/intena words *)
    let a_noff := add_vec a0f (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_intena := add_vec a0f (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    (* the spinlock's fields *)
    let a_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    (* prologue register chain *)
    let A0 := <[Regidx csp_rs1 := regval_into_reg spd]> m in
    let A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0 in
    let A2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1 in
    (* push_off's entry map (after the jal's link write) *)
    let P0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 4)]> A2 in
    (* push_off's internal register chain (mirrors wp_push_off's lets) *)
    let PN0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (P0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> P0 in
    let PN1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (PN0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> PN0 in
    let PN2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read mstatus0)]> PN1 in
    let PN3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (PN2 !!! Regidx (mword_of_int 15 : mword 5)))]> PN2 in
    let PN4 := po_mycpu_out (mword_of_int (PO + 0x10)) PN3 in
    let PN5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noff)]> PN4 in
    let PN6 := po_mycpu_out (mword_of_int (PO + 0x2c)) PN5 in
    let PN7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (PN6 !!! Regidx (mword_of_int 9 : mword 5))
           (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))]> PN6 in
    let PN8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (PN7 !!! Regidx (mword_of_int 15 : mword 5))
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> PN7 in
    (* push_off's noff/intena update values (mirrors wp_push_off) *)
    let po_storeval32 := (autocast (T := mword)
        (subrange_vec_dec (PN8 !!! Regidx (mword_of_int 15 : mword 5)) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let po_noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 noff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let po_noff_store := (autocast (T := mword) (subrange_vec_dec po_noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    (* the return target *)
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    (* ---- S-mode configuration ---- *)
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
    legalize_sstatus_val mstatus0 (sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    (* ---- the amoswap data cell additionally supports amoswap.w ---- *)
    (forall pmar0, pma_allows_all pmar0 ->
       exists region_amo,
         matching_pma_region pmar0 (Physaddr lk) 4 = Some region_amo /\
         (override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_readable) = true /\
         (override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_writable) = true /\
         pma_allows_atomic_op
           ((override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_atomic_support))
           AMOSWAP 4 = true) ->
    (* ---- push_off's a0f pins (its two mycpu calls return &cpus[cpuid]) ---- *)
    po_mycpu_out (mword_of_int (PO + 0x10)) PN3 !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    po_mycpu_out (mword_of_int (PO + 0x2c)) PN5 !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    po_mycpu_out (mword_of_int (PO + 0x18)) PN5 !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    po_mycpu_out (mword_of_int (PO + 0x18)) PN8 !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    (* ---- fetch geometry: a single X-bit fact threaded to every instruction
       (covers acquire, push_off, holding, and both mycpu call sites); the
       RAM/PMP fetch geometry is derived internally from instr_bytes ---- *)
    po_mycpu_geom pmpcfg0 pmpaddr00 ->
    (* ---- the lock is not already held by THIS cpu (no panic) ---- *)
    eq_vec (cpuold : mword 64) (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) = false ->
    (* ---- data-slot geometry ---- *)
    po_slot_align a_r24 8 -> po_slot_align a_r16 8 -> po_slot_align a_r8 8 ->
    po_slot_align a_p24 8 -> po_slot_align a_p16 8 -> po_slot_align a_p8 8 ->
    po_slot_align a_fra 8 -> po_slot_align a_fs0 8 ->
    po_slot_geom root_ppn pmpaddr00 svpn_noff a_noff 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_intena a_intena 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_lk lk 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_cpu a_cpu 8 ->
    (* ---- the return target is well-aligned ---- *)
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is AQw -∗ gpr_file m -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_r24 j) ↦ₘ nth_byte vr24 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_r16 j) ↦ₘ nth_byte vr16 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_r8 j) ↦ₘ nth_byte vr8 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_p24 j) ↦ₘ nth_byte pr24 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_p16 j) ↦ₘ nth_byte pr16 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_p8 j) ↦ₘ nth_byte pr8 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_fra j) ↦ₘ nth_byte fraold j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_fs0 j) ↦ₘ nth_byte fs0old j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add a_noff j) ↦ₘ nth_byte noff j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add a_intena j) ↦ₘ nth_byte intena_old j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add lk j) ↦ₘ nth_byte lockv j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add a_cpu j) ↦ₘ nth_byte cpuold j) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
      mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      (∃ mfin, gpr_file mfin ∗
        ⌜ mfin !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5) /\
          mfin !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5) /\
          mfin !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5) /\
          mfin !!! Regidx csp_rs1 = m !!! Regidx csp_rs1 /\
          mfin !!! Regidx (mword_of_int 10 : mword 5)
            = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) ⌝) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add a_r24 j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 1 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add a_r16 j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 8 : mword 5)) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add a_r8 j) ↦ₘ nth_byte (m !!! Regidx (mword_of_int 9 : mword 5)) j) -∗
      (∃ (vp24 vp16 vp8 vfra vfs0 : bv 64),
        ([∗ list] j ∈ seq 0 8, (pa_add a_p24 j) ↦ₘ nth_byte vp24 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add a_p16 j) ↦ₘ nth_byte vp16 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add a_p8 j) ↦ₘ nth_byte vp8 j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add a_fra j) ↦ₘ nth_byte vfra j) ∗
        ([∗ list] j ∈ seq 0 8, (pa_add a_fs0 j) ↦ₘ nth_byte vfs0 j)) -∗
      ([∗ list] j ∈ seq 0 4, (pa_add a_noff j) ↦ₘ nth_byte po_noff_store j) -∗
      ([∗ list] j ∈ seq 0 4, (pa_add a_intena j) ↦ₘ
          nth_byte (if eq_vec (sign_extend' 64 noff) zero_reg then po_storeval32 else intena_old) j) -∗
      ([∗ list] j ∈ seq 0 4, (pa_add lk j) ↦ₘ nth_byte (mword_of_int 1 : mword 32) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add a_cpu j) ↦ₘ
          nth_byte (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros AQw lk sp0 spd a_r24 a_r16 a_r8 po_spd a_p24 a_p16 a_p8 po_spm10 a_fra a_fs0
      a_noff a_intena a_cpu A0 A1 A2 P0 PN0 PN1 PN2 PN3 PN4 PN5 PN6 PN7 PN8
      po_storeval32 po_noff_a5 po_noff_store ret_tgt
      HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hpmpp Hpteregion Halignp HW HR Hramcov
      Hlegal Hpma_amo Ha0_10 Ha0_2c Ha0_18f Ha0_18t Hmyg Hnotmine
      Hg_r24 Hg_r16 Hg_r8 Hg_p24 Hg_p16 Hg_p8 Hg_fra Hg_fs0
      Hg_noff Hg_intena Hg_lk Hg_cpu Hal0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv #Htext Hpc Hfile
             Hr24 Hr16 Hr8 Hp24 Hp16 Hp8 Hfra Hfs0 Hnoff Hintena Hlock Hcpu Hcont".
    iPoseProof (aqi_00 with "Htext") as "Hi00".
    iPoseProof (aqi_02 with "Htext") as "Hi02".
    iPoseProof (aqi_04 with "Htext") as "Hi04".
    iPoseProof (aqi_06 with "Htext") as "Hi06".
    iPoseProof (aqi_08 with "Htext") as "Hi08".
    iPoseProof (aqi_0a with "Htext") as "Hi0a".
    iPoseProof (aqi_0c with "Htext") as "Hi0c".
    iPoseProof (aqi_10 with "Htext") as "Hi10".
    iPoseProof (aqi_12 with "Htext") as "Hi12".
    iPoseProof (aqi_16 with "Htext") as "Hi16".
    iPoseProof (aqi_18 with "Htext") as "Hi18".
    iPoseProof (aqi_1a with "Htext") as "Hi1a".
    iPoseProof (aqi_1c with "Htext") as "Hi1c".
    iPoseProof (aqi_20 with "Htext") as "Hi20".
    iPoseProof (aqi_22 with "Htext") as "Hi22".
    iPoseProof (aqi_24 with "Htext") as "Hi24".
    iPoseProof (aqi_28 with "Htext") as "Hi28".
    iPoseProof (aqi_2a with "Htext") as "Hi2a".
    iPoseProof (aqi_2c with "Htext") as "Hi2c".
    iPoseProof (aqi_2e with "Htext") as "Hi2e".
    iPoseProof (aqi_30 with "Htext") as "Hi30".
    iPoseProof (aqi_32 with "Htext") as "Hi32".
    (* the entry pc in the canonical (AQ + 0x00) spelling *)
    assert (Hpc00 : (mword_of_int AQ : mword 64) = mword_of_int (AQ + 0x00))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite /AQw Hpc00) in "Hpc".
    (* slot-align components *)
    pose proof Hg_r24 as [R24a R24p]. pose proof Hg_r16 as [R16a R16p]. pose proof Hg_r8 as [R8a R8p].
    (* ---- 0x00: c.addi sp,-32 ---- *)
    iApply (wp_caddi_gpr_s_config root_ppn E Φ (mword_of_int (AQ + 0x00)) csp_rs1 (mword_of_int 32 : mword 6) m
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpp02 : add_vec_int (mword_of_int (AQ + 0x00) : mword 64) 2 = mword_of_int (AQ + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    assert (Hcsp0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0; apply lookup_total_insert).
    (* ---- 0x02: c.sdsp ra,24(sp) ---- *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (AQ + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 vr24 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HW
              ltac:(rewrite Hcsp0; exact R24a) ltac:(rewrite Hcsp0; exact R24p)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi02 [Hr24] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr24". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr24".
    assert (HA0ra : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hcsp0 HA0ra) in "Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (AQ + 0x02) : mword 64) 2 = mword_of_int (AQ + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,16(sp) ---- *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (AQ + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 vr16 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HW
              ltac:(rewrite Hcsp0; exact R16a) ltac:(rewrite Hcsp0; exact R16p)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi04 [Hr16] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr16". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr16".
    assert (HA0s0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hcsp0 HA0s0) in "Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (AQ + 0x04) : mword 64) 2 = mword_of_int (AQ + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.sdsp s1,8(sp) ---- *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (AQ + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 vr8 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HW
              ltac:(rewrite Hcsp0; exact R8a) ltac:(rewrite Hcsp0; exact R8p)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi06 [Hr8] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr8". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr8".
    assert (HA0s1 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hcsp0 HA0s1) in "Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (AQ + 0x06) : mword 64) 2 = mword_of_int (AQ + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ (mword_of_int (AQ + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpp0a : add_vec_int (mword_of_int (AQ + 0x08) : mword 64) 2 = mword_of_int (AQ + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ---- 0x0a: c.mv s1,a0 ---- *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (AQ + 0x0a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              A1 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1) with A2.
    assert (Hpp0c : add_vec_int (mword_of_int (AQ + 0x0a) : mword 64) 2 = mword_of_int (AQ + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* ---- 0x0c: jal ra,push_off ---- *)
    iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                 with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
      as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
    assert (EQ0e : add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 2 = mword_of_int (AQ + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_gpr_s root_ppn E Φ (mword_of_int (AQ + 0x0c)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fffba : mword 21)
              A2 pmpcfg0 pmpaddr00 region_pte (1/2)%Qp
              HN Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hsm Hpca Hpaa Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 4)]> A2) with P0.
    assert (Htgtpo : add_vec (mword_of_int (AQ + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 0x1fffba : mword 21)) = mword_of_int (PO + 0x00))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtpo) in "Hpc".
    iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                 with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
      as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
    (* ---- push_off ---- *)
    assert (HP0csp : P0 !!! Regidx csp_rs1 = spd).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hcsp0. }
    assert (HP0ra : P0 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 4)
      by (rewrite /P0; apply lookup_total_insert).
    assert (E1a : add_vec_int (mword_of_int (PO + 0x18) : mword 64) 2 = mword_of_int (PO + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_push_off root_ppn E Φ P0 svpn_noff svpn_intena pr24 pr16 pr8 fraold fs0old noff intena_old a0f
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hpmpp Hpteregion Halignp HW HR Hramcov
              Hlegal ltac:(vm_compute; reflexivity)
              ltac:(rewrite HP0ra; vm_compute; reflexivity)
              Ha0_10 Ha0_2c Ha0_18f Ha0_18t Hmyg
              ltac:(rewrite HP0csp; exact Hg_p24) ltac:(rewrite HP0csp; exact Hg_p16) ltac:(rewrite HP0csp; exact Hg_p8)
              ltac:(rewrite HP0csp; exact Hg_fra) ltac:(rewrite HP0csp; exact Hg_fs0)
              Hg_noff Hg_intena
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile [Hp24] [Hp16] [Hp8] [Hfra] [Hfs0] [Hnoff] [Hintena] [-]").
    { iEval (rewrite HP0csp). iExact "Hp24". }
    { iEval (rewrite HP0csp). iExact "Hp16". }
    { iEval (rewrite HP0csp). iExact "Hp8". }
    { iEval (rewrite HP0csp). iExact "Hfra". }
    { iEval (rewrite HP0csp). iExact "Hfs0". }
    { iExact "Hnoff". }
    { iExact "Hintena". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hmfin Hp24 Hp16 Hp8 Hjunk Hnoff Hintena".
    iEval (rewrite HP0csp) in "Hp24". iEval (rewrite HP0csp) in "Hp16". iEval (rewrite HP0csp) in "Hp8".
    iEval (rewrite HP0csp) in "Hjunk".
    assert (Hpc10 : update_vec_dec (add_vec (P0 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AQ + 0x10))
      by (rewrite HP0ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    iDestruct "Hmfin" as (mfin) "[Hfile %Hmf]".
    destruct Hmf as (Hfra_ & Hfs0_ & Hfs1_ & Hfsp_ & Hftp_).
    (* canonical values of the tracked registers after push_off *)
    assert (HP0s1 : P0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert.
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0tp : P0 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0s0 : P0 !!! Regidx (mword_of_int 8 : mword 5) = A1 !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    rewrite HP0s1 in Hfs1_. rewrite HP0csp in Hfsp_. rewrite HP0tp in Hftp_. rewrite HP0ra in Hfra_.
    (* ---- 0x10: c.mv a0,s1 ---- *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (AQ + 0x10)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              mfin mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi10 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (B1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfin !!! Regidx (mword_of_int 9 : mword 5)))]> mfin).
    assert (Hpp12 : add_vec_int (mword_of_int (AQ + 0x10) : mword 64) 2 = mword_of_int (AQ + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ---- 0x12: jal ra,holding ---- *)
    iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                 with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
      as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
    assert (EQ14 : add_vec_int (mword_of_int (AQ + 0x12) : mword 64) 2 = mword_of_int (AQ + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_gpr_s root_ppn E Φ (mword_of_int (AQ + 0x12)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fff88 : mword 21)
              B1 pmpcfg0 pmpaddr00 region_pte (1/2)%Qp
              HN Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hsm Hpca Hpaa Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
    set (B2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AQ + 0x12) : mword 64) 4)]> B1).
    assert (Htgtho : add_vec (mword_of_int (AQ + 0x12) : mword 64) (sign_extend' 64 (mword_of_int 0x1fff88 : mword 21)) = mword_of_int KernelSyms.holding)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtho) in "Hpc".
    iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                 with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
      as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
    (* ---- holding() (fast path) ---- *)
    assert (HB2a0 : B2 !!! Regidx (mword_of_int 10 : mword 5) = add_vec zero_reg (add_vec zero_reg lk)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert. rewrite Hfs1_. reflexivity. }
    assert (HB2ra : B2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AQ + 0x12) : mword 64) 4)
      by (rewrite /B2; apply lookup_total_insert).
    assert (Eh2 : add_vec_int (mword_of_int KernelSyms.holding : mword 64) 2 = mword_of_int (KernelSyms.holding + 2))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eh4 : add_vec_int (mword_of_int KernelSyms.holding : mword 64) 4 = mword_of_int (KernelSyms.holding + 4))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eh6 : add_vec_int (mword_of_int KernelSyms.holding : mword 64) 6 = mword_of_int (KernelSyms.holding + 6))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (HAlk : add_vec (B2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = lk).
    { rewrite HB2a0. rewrite !aq_addv_zero_l.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* address bridges into wp_holding's own lets *)
    assert (HB2sp : B2 !!! Regidx csp_rs1 = spd).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfsp_. }
    assert (HB2tp : B2 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hftp_. }
    assert (HAcpu2 : add_vec (B2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = a_cpu)
      by (rewrite HB2a0 !aq_addv_zero_l; reflexivity).
    assert (Hspdh_eq : add_vec (B2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = po_spd)
      by (rewrite HB2sp; reflexivity).
    iDestruct "Hjunk" as (vfra0 vfs00) "[Hfra2 Hfs02]".
    iApply (wp_holding root_ppn E Φ B2 svpn_lk svpn_cpu lockv cpuold
              (P0 !!! Regidx (mword_of_int 1 : mword 5)) (P0 !!! Regidx (mword_of_int 8 : mword 5))
              (P0 !!! Regidx (mword_of_int 9 : mword 5)) vfra0 vfs00
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              (dqm:=DfracOwn 1) (dqc:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
              Hpmpp Hpteregion Halignp HW HR Hramcov
              Hmyg
              ltac:(rewrite HAlk; exact Hg_lk)
              ltac:(rewrite HAcpu2; exact Hg_cpu)
              ltac:(rewrite Hspdh_eq; exact Hg_p24)
              ltac:(rewrite Hspdh_eq; exact Hg_p16)
              ltac:(rewrite Hspdh_eq; exact Hg_p8)
              ltac:(rewrite Hspdh_eq; exact Hg_fra)
              ltac:(rewrite Hspdh_eq; exact Hg_fs0)
              ltac:(rewrite HB2tp; exact Hnotmine)
              ltac:(rewrite HB2ra; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile
                    [Hlock] [Hcpu] [Hp24] [Hp16] [Hp8] [Hfra2] [Hfs02] [-]").
    { iEval (rewrite HAlk). iExact "Hlock". }
    { iEval (rewrite HAcpu2). iExact "Hcpu". }
    { iEval (rewrite Hspdh_eq). iExact "Hp24". }
    { iEval (rewrite Hspdh_eq). iExact "Hp16". }
    { iEval (rewrite Hspdh_eq). iExact "Hp8". }
    { iEval (rewrite Hspdh_eq). iExact "Hfra2". }
    { iEval (rewrite Hspdh_eq). iExact "Hfs02". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hmh Hlock Hcpu Hhj".
    iEval (rewrite HAlk) in "Hlock".
    iEval (rewrite HAcpu2) in "Hcpu".
    iDestruct "Hmh" as (mh) "[Hfile %Hmhf]".
    destruct Hmhf as (Hhra & Hhs0 & Hms1 & Hmsp & Hmtp & Hma0).
    iDestruct "Hhj" as (w24 w16 w8 wra ws0) "(Hp24 & Hp16 & Hp8 & Hfra & Hfs0)".
    iEval (rewrite Hspdh_eq) in "Hp24". iEval (rewrite Hspdh_eq) in "Hp16".
    iEval (rewrite Hspdh_eq) in "Hp8". iEval (rewrite Hspdh_eq) in "Hfra".
    iEval (rewrite Hspdh_eq) in "Hfs0".
    assert (Hpc16 : update_vec_dec (add_vec (B2 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AQ + 0x16))
      by (rewrite HB2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- 0x16: c.li a4,1 ---- *)
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ (mword_of_int (AQ + 0x16)) (mword_of_int 14 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 14 : mword 5)
              (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 14), ADDI))
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
              mh mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi16 [-]").
    { intros s_pc Hnpc _ _.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) (mword_of_int 14) (sign_extend' 12 (mword_of_int 1 : mword 6)) s_pc).
      replace (Z.eqb (uint (mword_of_int 14 : mword 5)) 0) with false by (vm_compute; reflexivity).
      unfold gpr_addi_val.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true by (vm_compute; reflexivity).
      reflexivity. }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (B5 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> mh).
    assert (Hpp18 : add_vec_int (mword_of_int (AQ + 0x16) : mword 64) 2 = mword_of_int (AQ + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* ---- 0x18: c.bnez a0 (NOT taken: a0 = 0) ---- *)
    assert (HB5a0 : B5 !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)).
    { rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hma0. }
    iApply (wp_cbnez_fall_s root_ppn E Φ (mword_of_int (AQ + 0x18)) (mword_of_int 14) (Cregidx (mword_of_int 2)) (mword_of_int 10)
              B5 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite HB5a0; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi18 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (Hpp1a : add_vec_int (mword_of_int (AQ + 0x18) : mword 64) 2 = mword_of_int (AQ + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* ---- 0x1a: c.mv a5,a4 ---- *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (AQ + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              B5 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (B6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec zero_reg (B5 !!! Regidx (mword_of_int 14 : mword 5)))]> B5).
    assert (Hpp1c : add_vec_int (mword_of_int (AQ + 0x1a) : mword 64) 2 = mword_of_int (AQ + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* ---- 0x1c: amoswap.w.aq a5,a5,(s1) ---- *)
    assert (HB2s1 : B2 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfs1_. }
    assert (HB6s1 : B6 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /B6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms1. exact HB2s1. }
    assert (HAlk2 : add_vec (B6 !!! Regidx (mword_of_int 9 : mword 5)) (zeros' 64) = lk).
    { rewrite HB6s1. rewrite aq_addv_zero_l.
      replace (zeros' 64 : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    pose proof Hg_lk as (Lcanon & Lvpn & Lident & Lmask & Lvpn2 & Lmvpn & Lmppn & Lrange & Lalign & Lpalign).
    iApply (wp_amoswap_w_s root_ppn E Φ (mword_of_int (AQ + 0x1c)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 9)
              svpn_lk B6 lockv mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg
              Hramcov
              ltac:(rewrite HAlk2; exact Lcanon) ltac:(rewrite HAlk2; exact Lvpn) ltac:(rewrite HAlk2; exact Lident)
              Lmask Lvpn2 Lmvpn Lmppn Hpmpp Hpteregion Halignp
              ltac:(rewrite HAlk2; exact Lrange) HR HW
              ltac:(rewrite HAlk2; exact Hpma_amo)
              ltac:(rewrite HAlk2; exact Lalign) ltac:(rewrite HAlk2; exact Lpalign)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1c [Hlock] [-]").
    { iEval (rewrite HAlk2). iExact "Hlock". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hlock".
    iEval (rewrite HAlk2) in "Hlock".
    set (B7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (amoswap_loaded lockv)]> B6).
    (* the stored lock word is 1 *)
    assert (HB6a5 : B6 !!! Regidx (mword_of_int 15 : mword 5)
                    = add_vec zero_reg (B5 !!! Regidx (mword_of_int 14 : mword 5)))
      by (rewrite /B6; apply lookup_total_insert).
    assert (HB5a4 : B5 !!! Regidx (mword_of_int 14 : mword 5)
                    = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (rewrite /B5; apply lookup_total_insert).
    assert (Hstored1 : amoswap_stored (B6 !!! Regidx (mword_of_int 15 : mword 5)) = (mword_of_int 1 : mword 32)).
    { rewrite HB6a5 HB5a4. apply bv_eq. vm_compute. reflexivity. }
    iEval (rewrite Hstored1) in "Hlock".
    assert (Hpp20 : add_vec_int (mword_of_int (AQ + 0x1c) : mword 64) 4 = mword_of_int (AQ + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* ---- 0x20: sext.w a5 ---- *)
    iApply (wp_caddiw_s root_ppn E Φ (mword_of_int (AQ + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6) B7
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi20 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (B8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (B7 !!! Regidx (mword_of_int 15 : mword 5))
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> B7).
    assert (Hpp22 : add_vec_int (mword_of_int (AQ + 0x20) : mword 64) 2 = mword_of_int (AQ + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* ---- 0x22: c.bnez a5 -- a5 = sext64 lockv: the two paths diverge ---- *)
    assert (HB7a5 : B7 !!! Regidx (mword_of_int 15 : mword 5) = amoswap_loaded lockv)
      by (rewrite /B7; apply lookup_total_insert).
    assert (HB8a5 : B8 !!! Regidx (mword_of_int 15 : mword 5)
                    = sign_extend' 64 (subrange_vec_dec (add_vec (B7 !!! Regidx (mword_of_int 15 : mword 5))
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))
      by (rewrite /B8; apply lookup_total_insert).
    assert (HB8a5s : B8 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 lockv).
    { rewrite HB8a5 HB7a5. apply aq_sextw_round. }
    destruct (neq_vec (sign_extend' 64 lockv) zero_reg) eqn:Hheld.
    - (* ===== the lock was HELD: c.bnez TAKEN back to +0x1a; the loop spins
         forever (Löb induction, wp_acquire_spin), and the write left the
         lock word 1 -- so the WP holds with no continuation. ===== *)
      iApply (wp_cbnez_taken_s root_ppn E Φ (mword_of_int (AQ + 0x22)) (mword_of_int 252) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                B8 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HB8a5s; exact Hheld)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi22 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      assert (Htgt14 : add_vec (mword_of_int (AQ + 0x22) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
              = mword_of_int (AQ + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt14) in "Hpc".
      (* collapse the a5 insert chain: B8 = <[a5 := sextw(...)]> B5 *)
      assert (HmapEq : B8 = <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec (add_vec (amoswap_loaded lockv)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> B5).
      { rewrite /B8 HB7a5 /B7 /B6 !insert_insert. reflexivity. }
      iEval (rewrite HmapEq) in "Hfile".
      assert (HB5a4L : B5 !!! Regidx (mword_of_int 14 : mword 5)
                      = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
        by (rewrite /B5; apply lookup_total_insert).
      assert (HB5s1 : B5 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
      { rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hms1. exact HB2s1. }
      iApply (wp_acquire_spin root_ppn E Φ B5 _ lk svpn_lk
                mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
                HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hpmpp Hpteregion Halignp HR HW
                Hmyg Hramcov Hg_lk Hpma_amo
                HB5a4L HB5s1
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile Hlock").
    - (* ===== the lock was FREE: c.bnez NOT taken; acquire() returns ===== *)
      iApply (wp_cbnez_fall_s root_ppn E Φ (mword_of_int (AQ + 0x22)) (mword_of_int 252) (Cregidx (mword_of_int 7)) (mword_of_int 15)
              B8 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite HB8a5s; exact Hheld)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi22 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (Hpp24 : add_vec_int (mword_of_int (AQ + 0x22) : mword 64) 2 = mword_of_int (AQ + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* ---- 0x24: jal ra,mycpu; the whole mycpu() ---- *)
    assert (HB8sp : B8 !!! Regidx csp_rs1 = spd).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hmsp. exact HB2sp. }
    assert (HB9sp : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AQ + 0x24) : mword 64) 4)]> B8) !!! Regidx csp_rs1 = spd)
      by (rewrite lookup_total_insert_ne; [ exact HB8sp | vm_compute; discriminate ]).
    (* the mycpu frame slots coincide with push_off's r24/r16 cells *)
    assert (Hmra : add_vec (add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = a_p24).
    { rewrite /a_p24 /po_spd !po_addv_assoc. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hms0 : add_vec (add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = a_p16).
    { rewrite /a_p16 /po_spd !po_addv_assoc. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_pushoff_call_mycpu root_ppn E Φ (mword_of_int (AQ + 0x24)) (mword_of_int 0xcb8 : mword 21) B8
              w24 w16
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN ltac:(apply bv_eq; vm_compute; reflexivity) Hmyg
              ltac:(vm_compute; reflexivity)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
              Hpmpp Hpteregion Halignp
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              HW HR Hramcov
              ltac:(rewrite HB9sp Hmra; exact Hg_p24)
              ltac:(rewrite HB9sp Hms0; exact Hg_p16)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile Hi24 [Hp24] [Hp16] [-]").
    { iEval (rewrite HB9sp Hmra). iExact "Hp24". }
    { iEval (rewrite HB9sp Hms0). iExact "Hp16". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hp24 Hp16".
    iEval (rewrite HB9sp Hmra) in "Hp24". iEval (rewrite HB9sp Hms0) in "Hp16".
    iEval (rewrite lookup_total_insert) in "Hpc".
    assert (Hpc28 : update_vec_dec (add_vec (add_vec_int (mword_of_int (AQ + 0x24) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (AQ + 0x28) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    set (C1 := po_mycpu_out (mword_of_int (AQ + 0x24)) B8).
    (* ---- 0x28: c.sd a0,16(s1) : lk->cpu := &cpus[cpuid] ---- *)
    assert (HB8s1 : B8 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HB6s1. }
    assert (HC1s1 : C1 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /C1 po_mycpu_out_s1. exact HB8s1. }
    assert (HAcpu : add_vec (C1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = a_cpu).
    { rewrite HC1s1 aq_addv_zero_l. reflexivity. }
    pose proof Hg_cpu as (Ccanon & Cvpn & Cident & Cmask & Cvpn2 & Cmvpn & Cmppn & Crange & Calign & Cpalign).
    iApply (wp_csd_s root_ppn E Φ (mword_of_int (AQ + 0x28)) (mword_of_int 10) (mword_of_int 9)
              (mword_of_int 16) svpn_cpu C1 cpuold mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              ltac:(rewrite HAcpu; exact Ccanon) ltac:(rewrite HAcpu; exact Cvpn) ltac:(rewrite HAcpu; exact Cident)
              Cmask Cvpn2 Cmvpn Cmppn Hpmpp Hpteregion Halignp ltac:(rewrite HAcpu; exact Crange) HW
              ltac:(rewrite HAcpu; exact Calign) ltac:(rewrite HAcpu; exact Cpalign)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi28 [Hcpu] [-]").
    { iEval (rewrite HAcpu). iExact "Hcpu". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hcpu".
    iEval (rewrite HAcpu) in "Hcpu".
    (* the stored value is mycpu's return &cpus[cpuid] *)
    assert (HB8tp : B8 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hmtp. exact HB2tp. }
    assert (HC1a0 : C1 !!! Regidx (mword_of_int 10 : mword 5) = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))).
    { rewrite /C1 po_mycpu_out_a0 HB8tp. reflexivity. }
    iEval (rewrite HC1a0) in "Hcpu".
    assert (Hpp2a : add_vec_int (mword_of_int (AQ + 0x28) : mword 64) 2 = mword_of_int (AQ + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* ---- 0x2a: c.ldsp ra,24(sp) ---- *)
    assert (HC1sp : C1 !!! Regidx csp_rs1 = spd).
    { rewrite /C1 po_mycpu_out_csp. exact HB8sp. }
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (AQ + 0x2a)) (mword_of_int 3) (mword_of_int 1 : mword 5)
              C1 (m !!! Regidx (mword_of_int 1 : mword 5))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HR
              ltac:(rewrite HC1sp; exact R24a) ltac:(rewrite HC1sp; exact R24p)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2a [Hr24]").
    { iEval (rewrite HC1sp). iExact "Hr24". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr24".
    iEval (rewrite HC1sp) in "Hr24".
    set (D1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> C1).
    assert (HD1sp : D1 !!! Regidx csp_rs1 = spd)
      by (rewrite /D1; rewrite lookup_total_insert_ne; [ exact HC1sp | vm_compute; discriminate ]).
    assert (Hpp2c : add_vec_int (mword_of_int (AQ + 0x2a) : mword 64) 2 = mword_of_int (AQ + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* ---- 0x2c: c.ldsp s0,16(sp) ---- *)
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (AQ + 0x2c)) (mword_of_int 2) (mword_of_int 8 : mword 5)
              D1 (m !!! Regidx (mword_of_int 8 : mword 5))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HR
              ltac:(rewrite HD1sp; exact R16a) ltac:(rewrite HD1sp; exact R16p)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2c [Hr16]").
    { iEval (rewrite HD1sp). iExact "Hr16". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr16".
    iEval (rewrite HD1sp) in "Hr16".
    set (D2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> D1).
    assert (HD2sp : D2 !!! Regidx csp_rs1 = spd)
      by (rewrite /D2; rewrite lookup_total_insert_ne; [ exact HD1sp | vm_compute; discriminate ]).
    assert (Hpp2e : add_vec_int (mword_of_int (AQ + 0x2c) : mword 64) 2 = mword_of_int (AQ + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* ---- 0x2e: c.ldsp s1,8(sp) ---- *)
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (AQ + 0x2e)) (mword_of_int 1) (mword_of_int 9 : mword 5)
              D2 (m !!! Regidx (mword_of_int 9 : mword 5))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HR
              ltac:(rewrite HD2sp; exact R8a) ltac:(rewrite HD2sp; exact R8p)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2e [Hr8]").
    { iEval (rewrite HD2sp). iExact "Hr8". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr8".
    iEval (rewrite HD2sp) in "Hr8".
    set (D3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> D2).
    assert (HD3sp : D3 !!! Regidx csp_rs1 = spd)
      by (rewrite /D3; rewrite lookup_total_insert_ne; [ exact HD2sp | vm_compute; discriminate ]).
    assert (Hpp30 : add_vec_int (mword_of_int (AQ + 0x2e) : mword 64) 2 = mword_of_int (AQ + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* ---- 0x30: c.addi16sp sp,32 ---- *)
    iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                 with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
      as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
    iApply (wp_caddi16sp_gpr_s root_ppn E Φ (mword_of_int (AQ + 0x30)) (mword_of_int 2 : mword 6) D3
              pmpcfg0 pmpaddr00 region_pte (1/2)%Qp HN Hmyg Hramcov Hpmpp Hpteregion Halignp
              with "Hsm Hpca Hpaa Htlbinv Hpc Hfile Hi30 [-]").
    iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
    iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                 with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
      as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
    set (D4 := <[Regidx csp_rs1 := regval_into_reg (add_vec (D3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> D3).
    assert (Hpp32 : add_vec_int (mword_of_int (AQ + 0x30) : mword 64) 2 = mword_of_int (AQ + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* ---- 0x32: c.ret ---- *)
    assert (HD4ra : D4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /D1. apply lookup_total_insert. }
    iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (AQ + 0x32)) (mword_of_int 1 : mword 5) D4
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
              ltac:(vm_compute; discriminate) Hlpe
              ltac:(rewrite HD4ra; exact Hal0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi32 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    iEval (rewrite HD4ra) in "Hpc".
    (* ---- hand everything to the caller's continuation ---- *)
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc [Hfile] Hr24 Hr16 Hr8 [Hfra Hfs0 Hp24 Hp16 Hp8] Hnoff Hintena Hlock Hcpu").
    { iExists D4. iFrame "Hfile". iPureIntro.
      split; [exact HD4ra|]. split; [|split; [|split]].
      - rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. apply lookup_total_insert.
      - rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. apply lookup_total_insert.
      - rewrite /D4. rewrite lookup_total_insert. rewrite HD3sp.
        rewrite /spd po_addv_assoc.
        replace (add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))
          with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        apply kv_addv_zero.
      - rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HC1a0.
    }
    iExists _, _, _, _, _.
    iFrame "Hp24 Hp16 Hp8 Hfra Hfs0".
  Qed.

End WpAcquireTop.
