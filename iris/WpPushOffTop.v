(* WpPushOffTop.v -- the top-level WP for xv6's push_off() in S-mode.
   Composes: the prologue/epilogue stack ops, csrrci (interrupt disable,
   WpPushOffCsr), the two mycpu() calls (WpMycpu), the per-cpu noff/intena
   4-byte accesses (WpPushOffMem), the beqz two-arm join, and the new
   arithmetic/branch instruction lemmas (WpPushOff).  Full functional
   postcondition: SIE cleared, noff incremented, intena = old SIE iff noff
   was 0, callee-saved restored, return to caller. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
From iris.base_logic.lib Require Import ghost_var.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import WpGprCsrwCommon.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode WpLeafCommon KernelText.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew.
Require Import WpPushOffCsr WpMycpu WpCallMycpu.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import WpRvcBridge KernelRvcDecode.
(* QUALIFIED (no Import): sstatus SIE-bit bridges for the saved-intena = 0 fact. *)
Require WpGprCsrwC.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Export WpSmodeLeafBase WpSmodeAddiw WpSmodeShiftiop WpSmodeRtype WpSmodeItype WpSmodeJal WpSmodeJalr WpSmodeCsr WpSmodeLoad WpSmodeStore WpSmodeBtype.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode templates (mirrors of WpMycpu / WpTimerinit / WpKvInstr).       *)
(* ===================================================================== *)
Local Ltac po_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac po_close1 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; po_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

Local Ltac po_close_ld s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (Defs.and_boolM (returnM _)
                          (currentlyEnabled Ext_Zca))) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; po_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

Local Ltac po_close0 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; po_ast
  | apply (exec_currentlyEnabled_Zca s HmisaC) ].

(* ---- RVC decodes ---- *)

(* podec_lw (c.lw a5,120(a0)) is shared with pop_off — now in KernelRvcDecode. *)

(* +0x16  0xcb99  c.beqz a5,80000bec *)
Lemma podec_16 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcb99 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 11, Cregidx (mword_of_int 7)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x1e  0x2785  c.addiw a5,a5,1 *)
Lemma podec_1e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2785 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 1, Regidx (mword_of_int 15)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* podec_sw120 (c.sw a5,120(a0)) is shared with pop_off — now in KernelRvcDecode. *)

(* +0x36  0xdd7c  c.sw a5,124(a0) *)
Lemma podec_sw124 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xdd7c : mword 16)) s
  = Some (C_SW (mword_of_int 31, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x34  0x8b85  c.andi a5,a5,1 *)
Lemma podec_34 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8b85 : mword 16)) s
  = Some (C_ANDI (mword_of_int 1, Cregidx (mword_of_int 7)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x38  0xb7c5  c.j 80000bd8 *)
Lemma podec_38 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb7c5 : mword 16)) s
  = Some (C_J (mword_of_int 2032 : mword 11), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* ---- base (4-byte) decodes ----
   [decode_any]'s final [reflexivity] fails here: [vm_compute] reduces BOTH
   sides to [@BV] literals whose [BvWf] proof fields differ (proof-irrelevant
   but not definitionally equal).  Reduce only the LHS, then close each bv leaf
   with [bv_eq] (value-only). *)
Local Ltac po_dbase s Hpriv :=
  decode_pause_prefix s Hpriv;
  match goal with |- ?lhs = ?rhs =>
    let l := eval vm_compute in lhs in change_no_check (l = rhs) end;
  po_ast.

(* +0x0a  0x100177f3  csrrci a5,sstatus,2 *)
Lemma podec_0a s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x100177f3 : mword 32)) s
  = Some (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 15), CSRRC), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; po_dbase s Hpriv ]. Qed.

(* +0x10  0x507000ef  jal ra,mycpu *)
Lemma podec_10 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x507000ef : mword 32)) s
  = Some (JAL (mword_of_int 0xd06 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; po_dbase s Hpriv ]. Qed.

(* +0x18  0x4ff000ef  jal ra,mycpu *)
Lemma podec_18 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4ff000ef : mword 32)) s
  = Some (JAL (mword_of_int 0xcfe : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; po_dbase s Hpriv ]. Qed.

(* +0x2c  0x4eb000ef  jal ra,mycpu *)
Lemma podec_2c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4eb000ef : mword 32)) s
  = Some (JAL (mword_of_int 0xcea : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; po_dbase s Hpriv ]. Qed.

(* +0x30  0x0014d793  srli a5,s1,1 *)
Lemma podec_30 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0014d793 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 1 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 15), SRLI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; po_dbase s Hpriv ]. Qed.

(* ===================================================================== *)
(* po_imm120, poexec_lw, poexec_sw120 are shared with pop_off — now in
   KernelRvcDecode.  po_imm124/poexec_sw124 below are push_off-specific. *)
Lemma po_imm124 : zero_extend' 12 (concat_vec (mword_of_int 31 : mword 5) ('b"00")) = (mword_of_int 124 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma poexec_sw124 s :
  exec (execute (C_SW (mword_of_int 31, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 124, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_SW. cbn zeta.
  rewrite exec_returnM. rewrite po_cr2. rewrite po_cr7. rewrite po_imm124. reflexivity.
Qed.

Lemma poexec_andi s :
  exec (execute (C_ANDI (mword_of_int 1, Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_ANDI. cbn zeta.
  rewrite exec_returnM. rewrite !po_cr7. reflexivity.
Qed.


(* named form of wp_mycpu's output register file (= call_mycpu's m11 chain),
   so downstream geometry can reference its a0/sp lookups. *)
(* po_addv_assoc (add_vec associativity) is shared with pop_off — now in KernelRvcDecode. *)


(* ===================================================================== *)
(* SIE=0 (folded into smode_config) collapses push_off's saved-interrupt   *)
(* store [storeval32] to the concrete [zeros' 32], so wp_push_off's intena  *)
(* postcondition needs no mstatus0.  Bridges mirror WpAcquireLock.          *)
(* ===================================================================== *)

Lemma po_addv_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite bv_add_unsigned.
  change (bv_unsigned zero_reg) with 0.
  rewrite Z.add_0_l. apply bv_wrap_bv_unsigned.
Qed.

Lemma po_sstatus_bit1_sie (m : mword 64) :
  eq_vec (_get_Mstatus_SIE m) ('b"1") = false ->
  Z.testbit (bv_unsigned (sstatus_read m)) 1 = false.
Proof.
  intro HSIE.
  assert (Hz : _get_Mstatus_SIE m = ('b"0" : mword 1)) by (apply mword1_zero_of_ne_one; exact HSIE).
  unfold sstatus_read. rewrite WpGprCsrwC.subrange_full.
  apply WpGprCsrwC.sie_bit. rewrite WpGprCsrwC.mSIE_lower. exact Hz.
Qed.

Lemma po_storeval32_zero (m : mword 64) :
  eq_vec (_get_Mstatus_SIE m) ('b"1") = false ->
  (autocast (T := mword)
     (subrange_vec_dec
        (and_vec
           (shift_bits_right (add_vec zero_reg (sstatus_read m))
              (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
        (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = zeros' 32.
Proof.
  intro HSIE.
  pose proof (po_sstatus_bit1_sie m HSIE) as Hb1.
  assert (Hshamt : int_of_mword false (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0) = 1)
    by (vm_compute; reflexivity).
  assert (Hmask : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)) : mword 64) = 1)
    by (vm_compute; reflexivity).
  assert (Hsh0 : Z.testbit (bv_unsigned (shiftr (sstatus_read m) 1)) 0 = false).
  { unfold shiftr, with_word, MachineWord.logical_shift_right.
    rewrite bv_shiftr_unsigned.
    assert (Hn1 : bv_unsigned (MachineWord.N_to_word (MachineWord.Z_idx 64) (MachineWord.Z_idx 1)) = 1)
      by (vm_compute; reflexivity).
    rewrite Hn1. rewrite (Z.shiftr_spec (bv_unsigned (sstatus_read m)) 1 0 ltac:(lia)). simpl (0 + 1)%Z. exact Hb1. }
  assert (Hand0 : and_vec (shift_bits_right (add_vec zero_reg (sstatus_read m))
                    (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) = (zeros' 64 : mword 64)).
  { rewrite po_addv_zero_l. unfold shift_bits_right. rewrite Hshamt.
    apply bv_eq.
    assert (Hz64 : bv_unsigned (zeros' 64 : mword 64) = 0) by (vm_compute; reflexivity).
    rewrite Hz64. rewrite WpGprCsrwC.and_vec_unsigned. rewrite Hmask.
    apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec. rewrite Z.bits_0.
    destruct (decide (j = 0)) as [->|Hne].
    - rewrite Hsh0. reflexivity.
    - assert (Ht1 : Z.testbit 1 j = false)
        by (apply Z.bits_above_log2; [lia| change (Z.log2 1) with 0; lia]).
      rewrite Ht1. apply andb_false_r. }
  rewrite Hand0. apply bv_eq. vm_compute. reflexivity.
Qed.

Section WpPushOffTop.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the push_off instructions from [kernel_text].      *)
  (* ------------------------------------------------------------------- *)
  Notation PO := KernelSyms.push_off.

  Lemma poi_00 : kernel_text -∗ instr (mword_of_int (PO + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PO + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (PO + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) podec_00 exec_execute_C_ADDI. Qed.

  Lemma poi_02 : kernel_text -∗ instr (mword_of_int (PO + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PO + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (PO + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) podec_02 exec_execute_C_SDSP. Qed.

  Lemma poi_04 : kernel_text -∗ instr (mword_of_int (PO + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PO + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (PO + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) podec_04 exec_execute_C_SDSP. Qed.

  Lemma poi_06 : kernel_text -∗ instr (mword_of_int (PO + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (PO + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (PO + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) podec_06 exec_execute_C_SDSP. Qed.

  Lemma poi_08 : kernel_text -∗ instr (mword_of_int (PO + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PO + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (PO + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) podec_08 exec_execute_C_ADDI4SPN. Qed.

  Lemma poi_0a : kernel_text -∗ instr (mword_of_int (PO + 0x0a) : mword 64) false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 15), CSRRC)).
  Proof. mk_base (PO + 0x0a)%Z (mword_of_int 0x100177f3 : mword 32)
    (mword_of_int (PO + 0x0a) : mword 64) (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 15), CSRRC)) podec_0a. Qed.

  Lemma poi_0e : kernel_text -∗ instr (mword_of_int (PO + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (PO + 0x0e)%Z (mword_of_int 0x84be : mword 16)
    (mword_of_int (PO + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)) podec_0e exec_execute_C_MV. Qed.

  Lemma poi_10 : kernel_text -∗ instr (mword_of_int (PO + 0x10) : mword 64) false (JAL (mword_of_int 0xd06 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PO + 0x10)%Z (mword_of_int 0x507000ef : mword 32)
    (mword_of_int (PO + 0x10) : mword 64) (JAL (mword_of_int 0xd06 : mword 21, Regidx (mword_of_int 1))) podec_10. Qed.

  Lemma poi_14 : kernel_text -∗ instr (mword_of_int (PO + 0x14) : mword 64) true (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (PO + 0x14)%Z (mword_of_int 0x5d3c : mword 16)
    (mword_of_int (PO + 0x14) : mword 64) (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) podec_lw poexec_lw. Qed.

  Lemma poi_16 : kernel_text -∗ instr (mword_of_int (PO + 0x16) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (PO + 0x16)%Z (mword_of_int 0xcb99 : mword 16)
    (mword_of_int (PO + 0x16) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) podec_16 exec_execute_C_BEQZ. Qed.

  Lemma poi_18 : kernel_text -∗ instr (mword_of_int (PO + 0x18) : mword 64) false (JAL (mword_of_int 0xcfe : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PO + 0x18)%Z (mword_of_int 0x4ff000ef : mword 32)
    (mword_of_int (PO + 0x18) : mword 64) (JAL (mword_of_int 0xcfe : mword 21, Regidx (mword_of_int 1))) podec_18. Qed.

  Lemma poi_1c : kernel_text -∗ instr (mword_of_int (PO + 0x1c) : mword 64) true (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (PO + 0x1c)%Z (mword_of_int 0x5d3c : mword 16)
    (mword_of_int (PO + 0x1c) : mword 64) (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) podec_lw poexec_lw. Qed.

  Lemma poi_1e : kernel_text -∗ instr (mword_of_int (PO + 0x1e) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (PO + 0x1e)%Z (mword_of_int 0x2785 : mword 16)
    (mword_of_int (PO + 0x1e) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) podec_1e exec_execute_C_ADDIW. Qed.

  Lemma poi_20 : kernel_text -∗ instr (mword_of_int (PO + 0x20) : mword 64) true (STORE (mword_of_int 120, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)).
  Proof. mk_rvc (PO + 0x20)%Z (mword_of_int 0xdd3c : mword 16)
    (mword_of_int (PO + 0x20) : mword 64) (STORE (mword_of_int 120, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)) podec_sw120 poexec_sw120. Qed.

  Lemma poi_22 : kernel_text -∗ instr (mword_of_int (PO + 0x22) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PO + 0x22)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (PO + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) podec_22 exec_execute_C_LDSP. Qed.

  Lemma poi_24 : kernel_text -∗ instr (mword_of_int (PO + 0x24) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PO + 0x24)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (PO + 0x24) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) podec_24 exec_execute_C_LDSP. Qed.

  Lemma poi_26 : kernel_text -∗ instr (mword_of_int (PO + 0x26) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (PO + 0x26)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (PO + 0x26) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) podec_26 exec_execute_C_LDSP. Qed.

  Lemma poi_28 : kernel_text -∗ instr (mword_of_int (PO + 0x28) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (PO + 0x28)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (PO + 0x28) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) podec_28 exec_execute_C_ADDI16SP. Qed.

  Lemma poi_2a : kernel_text -∗ instr (mword_of_int (PO + 0x2a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PO + 0x2a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PO + 0x2a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) podec_2a exec_execute_C_JR. Qed.

  Lemma poi_2c : kernel_text -∗ instr (mword_of_int (PO + 0x2c) : mword 64) false (JAL (mword_of_int 0xcea : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PO + 0x2c)%Z (mword_of_int 0x4eb000ef : mword 32)
    (mword_of_int (PO + 0x2c) : mword 64) (JAL (mword_of_int 0xcea : mword 21, Regidx (mword_of_int 1))) podec_2c. Qed.

  Lemma poi_30 : kernel_text -∗ instr (mword_of_int (PO + 0x30) : mword 64) false (SHIFTIOP (mword_of_int 1 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 15), SRLI)).
  Proof. mk_base (PO + 0x30)%Z (mword_of_int 0x0014d793 : mword 32)
    (mword_of_int (PO + 0x30) : mword 64) (SHIFTIOP (mword_of_int 1 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 15), SRLI)) podec_30. Qed.

  Lemma poi_34 : kernel_text -∗ instr (mword_of_int (PO + 0x34) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_rvc (PO + 0x34)%Z (mword_of_int 0x8b85 : mword 16)
    (mword_of_int (PO + 0x34) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) podec_34 poexec_andi. Qed.

  Lemma poi_36 : kernel_text -∗ instr (mword_of_int (PO + 0x36) : mword 64) true (STORE (mword_of_int 124, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)).
  Proof. mk_rvc (PO + 0x36)%Z (mword_of_int 0xdd7c : mword 16)
    (mword_of_int (PO + 0x36) : mword 64) (STORE (mword_of_int 124, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)) podec_sw124 poexec_sw124. Qed.

  Lemma poi_38 : kernel_text -∗ instr (mword_of_int (PO + 0x38) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PO + 0x38)%Z (mword_of_int 0xb7c5 : mword 16)
    (mword_of_int (PO + 0x38) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")), zreg)) podec_38 exec_execute_C_J. Qed.

  (* ================================================================== *)
  (* [smode_config] wrappers for the raw leaves push_off/pop_off call,   *)
  (* so their bodies thread the bundle instead of the unbundled cells.   *)
  (* Each peels the config once and re-bundles in the continuation; the  *)
  (* instructions preserve every config cell.                            *)
  (* ================================================================== *)


  Lemma wp_clw_s_ram_scfg (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : mword 32) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    ea ↦₄{ dqm } v -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      ea ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ea Hrd.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_clw_s_ram root_ppn Φ pc rd rs1 imm m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
 Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_candi_s_scfg (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI)) -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (and_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_candi_s root_ppn Φ pc rd imm m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  (* The reusable jal->mycpu->return composites wp_call_mycpu /
     wp_call_mycpu_scfg_cs now live in WpMycpu (beside wp_mycpu), so
     holding/acquire reuse them without depending on push_off. *)

  (* ============ the suffix from 0x80000bd8 (PO+0x18) to c.ret ============ *)

  Lemma wp_push_off_suffix (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (ms : gmap regidx (mword 64))
      (noff : mword 32) (ra0e s00e s10e : mword 64)
      :
    let P : mword 64 := mword_of_int (PO + 0x18) in
    let spm := ms !!! Regidx csp_rs1 in
    let a0v := mycpu_ret (ms !!! Regidx (mword_of_int 4 : mword 5)) in
    let a8_noff := add_vec a0v (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a8_p24 := add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a8_p16 := add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a8_p8  := add_vec spm (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 noff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let storeval := (autocast (T := mword)
        (subrange_vec_dec noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let cret_tgt := update_vec_dec (add_vec ra0e (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    eq_vec (access_vec_dec cret_tgt 0) ('b"0") = true ->
    smode_config γ (DfracOwn 1) -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is P -∗ gpr_file ms -∗
    stack_own spm 2 -∗
    a8_noff ↦₄ noff -∗
    a8_p24 ↦₈ ra0e -∗
    a8_p16 ↦₈ s00e -∗
    a8_p8 ↦₈ s10e -∗
    ( smode_config γ (DfracOwn 1) -∗
      tlb_inv root_ppn -∗
      pc_is cret_tgt -∗
      (∃ mfin, gpr_file mfin ∗ ⌜ mfin !!! Regidx (mword_of_int 1 : mword 5) = ra0e /\
                                 mfin !!! Regidx (mword_of_int 8 : mword 5) = s00e /\
                                 mfin !!! Regidx (mword_of_int 9 : mword 5) = s10e /\
                                 mfin !!! Regidx csp_rs1 = add_vec spm (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) /\
                                 mfin !!! Regidx (mword_of_int 4 : mword 5) = ms !!! Regidx (mword_of_int 4 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 18 : mword 5) = ms !!! Regidx (mword_of_int 18 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 19 : mword 5) = ms !!! Regidx (mword_of_int 19 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 20 : mword 5) = ms !!! Regidx (mword_of_int 20 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 21 : mword 5) = ms !!! Regidx (mword_of_int 21 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 22 : mword 5) = ms !!! Regidx (mword_of_int 22 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 23 : mword 5) = ms !!! Regidx (mword_of_int 23 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 24 : mword 5) = ms !!! Regidx (mword_of_int 24 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 25 : mword 5) = ms !!! Regidx (mword_of_int 25 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 26 : mword 5) = ms !!! Regidx (mword_of_int 26 : mword 5) /\
                                 mfin !!! Regidx (mword_of_int 27 : mword 5) = ms !!! Regidx (mword_of_int 27 : mword 5) ⌝) -∗
      stack_own spm 2 -∗
      a8_noff ↦₄ storeval -∗
      a8_p24 ↦₈ ra0e -∗
      a8_p16 ↦₈ s00e -∗
      a8_p8 ↦₈ s10e -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros P spm a0v a8_noff a8_p24 a8_p16 a8_p8 noff_a5 storeval cret_tgt Hret0.
    set (s00 := ms !!! Regidx (mword_of_int 8 : mword 5)).
    assert (Hm0sp : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> ms) !!! Regidx csp_rs1 = spm)
      by (rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    iIntros "Hsm Htlbinv #Htext Hpc Hfile Hstk Hnoff Hpp24 Hpp16 Hpp8 Hcont".
    iPoseProof (poi_18 with "Htext") as "Hi18".
    iApply (wp_call_mycpu_scfg_cs root_ppn γ Φ P (mword_of_int 0xcfe : mword 21) ms
 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              with "Hsm Htlbinv Htext Hpc Hfile Hi18 [Hstk] [-]").
    { iEval (rewrite Hm0sp). iExact "Hstk". }
    iIntros (mo) "Hsm Htlbinv Hpc Hfile %Hmo Hstk".
    destruct Hmo as [Hmo_cs Hmo_a0].
    destruct Hmo_cs as (Hcsp & Htp & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
    set (M1 := mo).
    set (M2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noff)]> M1).
    set (M3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (M2 !!! Regidx (mword_of_int 15 : mword 5))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> M2).
    set (M4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M3).
    set (M5 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]> M4).
    set (M6 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg s10e]> M5).
    set (M7 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (M6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> M6).
    iEval (rewrite Hm0sp) in "Hstk".
    (* normalise pc = ret_tgt to PO+0x1c *)
    iEval (rewrite lookup_total_insert) in "Hpc".
    assert (Hpc1c : update_vec_dec (add_vec (add_vec_int P 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (PO + 0x1c) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* ---- 0x1c: c.lw a5,120(a0) : a5 := zext32(noff) ---- *)
    assert (Hm110 : M1 !!! Regidx (mword_of_int 10 : mword 5) = a0v) by exact Hmo_a0.
    iPoseProof (poi_1c with "Htext") as "Hi1c".
    iApply (wp_clw_s_ram_scfg root_ppn γ Φ (mword_of_int (PO + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) M1 noff
              (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi1c [Hnoff] [-]").
    { iEval (rewrite Hm110). iExact "Hnoff". }
    iIntros "Hsm Htlbinv Hpc Hfile Hnoff".
    iEval (rewrite Hm110) in "Hnoff".
    assert (Hpc1e : add_vec_int (mword_of_int (PO + 0x1c) : mword 64) 2 = mword_of_int (PO + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* ---- 0x1e: c.addiw a5,a5,1 : a5 := sext32(noff+1) ---- *)
    iPoseProof (poi_1e with "Htext") as "Hi1e".
    iApply (wp_caddiw_s_scfg root_ppn γ Φ (mword_of_int (PO + 0x1e)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6)
              M2 (dq:=DfracOwn 1)
  ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi1e [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    assert (Hpc20 : add_vec_int (mword_of_int (PO + 0x1e) : mword 64) 2 = mword_of_int (PO + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    (* ---- 0x20: c.sw a5,120(a0) : store noff+1 ---- *)
    assert (Hm310 : M3 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmo_a0. }
    iPoseProof (poi_20 with "Htext") as "Hi20".
    iApply (wp_csw_s_ram_scfg root_ppn γ Φ (mword_of_int (PO + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) M3 noff 
              (dq:=DfracOwn 1)

              with "Hsm Htlbinv Hpc Hfile Hi20 [Hnoff] [-]").
    { iEval (rewrite Hm310). iExact "Hnoff". }
    iIntros "Hsm Htlbinv Hpc Hfile Hnoff".
    assert (Hpc22 : add_vec_int (mword_of_int (PO + 0x20) : mword 64) 2 = mword_of_int (PO + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* ---- 0x22: c.ldsp ra,24(sp) : ra := ra0e ---- *)
    assert (Hcsp3 : M3 !!! Regidx csp_rs1 = spm).
    { rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hcsp. }
    iPoseProof (poi_22 with "Htext") as "Hi22".
    iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γ Φ (mword_of_int (PO + 0x22)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              M3 ra0e (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              
              with "Hsm Htlbinv Hpc Hfile Hi22 [Hpp24] [-]").
    { iEval (rewrite Hcsp3). iExact "Hpp24". }
    iIntros "Hsm Htlbinv Hpc Hfile Hpp24".
    assert (Hpc24 : add_vec_int (mword_of_int (PO + 0x22) : mword 64) 2 = mword_of_int (PO + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* ---- 0x24: c.ldsp s0,16(sp) : s0 := s00e ---- *)
    assert (Hcsp4 : M4 !!! Regidx csp_rs1 = spm).
    { rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hcsp3. }
    iPoseProof (poi_24 with "Htext") as "Hi24".
    iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γ Φ (mword_of_int (PO + 0x24)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              M4 s00e (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              
              with "Hsm Htlbinv Hpc Hfile Hi24 [Hpp16] [-]").
    { iEval (rewrite Hcsp4). iExact "Hpp16". }
    iIntros "Hsm Htlbinv Hpc Hfile Hpp16".
    assert (Hpc26 : add_vec_int (mword_of_int (PO + 0x24) : mword 64) 2 = mword_of_int (PO + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    (* ---- 0x26: c.ldsp s1,8(sp) : s1 := s10e ---- *)
    assert (Hcsp5 : M5 !!! Regidx csp_rs1 = spm).
    { rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hcsp4. }
    iPoseProof (poi_26 with "Htext") as "Hi26".
    iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γ Φ (mword_of_int (PO + 0x26)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              M5 s10e (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              
              with "Hsm Htlbinv Hpc Hfile Hi26 [Hpp8] [-]").
    { iEval (rewrite Hcsp5). iExact "Hpp8". }
    iIntros "Hsm Htlbinv Hpc Hfile Hpp8".
    assert (Hpc28 : add_vec_int (mword_of_int (PO + 0x26) : mword 64) 2 = mword_of_int (PO + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- 0x28: c.addi16sp sp,32 (via smode_config) ---- *)
    iPoseProof (poi_28 with "Htext") as "Hi28".
    iApply (wp_caddi16sp_gpr_s root_ppn γ Φ (mword_of_int (PO + 0x28)) (mword_of_int 2 : mword 6) M6
              1%Qp 
              with "Hsm Htlbinv Hpc Hfile Hi28 [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    assert (Hpc2a : add_vec_int (mword_of_int (PO + 0x28) : mword 64) 2 = mword_of_int (PO + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- 0x2a: c.ret : PC := ra0e (low bit cleared) ---- *)
    assert (Hra7 : M7 !!! Regidx (mword_of_int 1 : mword 5) = ra0e).
    { rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. apply lookup_total_insert. }
    iPoseProof (poi_2a with "Htext") as "Hi2a".
    iApply (wp_cret_s_zca_scfg root_ppn γ Φ (mword_of_int (PO + 0x2a)) (mword_of_int 1 : mword 5) M7
              (dq:=DfracOwn 1)
 
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra7; exact Hret0)
              with "Hsm Htlbinv Hpc Hfile Hi2a [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite Hra7) in "Hpc".
    (* ---- convert memory back to the postcondition addresses ---- *)
    assert (Hs00v : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> ms) !!! Regidx (mword_of_int 8 : mword 5) = s00)
      by (rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (HM315 : M3 !!! Regidx (mword_of_int 15 : mword 5) = noff_a5).
    { rewrite /M3 lookup_total_insert /M2 lookup_total_insert. reflexivity. }
    iEval (rewrite Hm310 HM315) in "Hnoff".
    iEval (rewrite Hcsp3) in "Hpp24".
    iEval (rewrite Hcsp4) in "Hpp16".
    iEval (rewrite Hcsp5) in "Hpp8".
    iApply ("Hcont" with "Hsm Htlbinv Hpc [Hfile] Hstk Hnoff Hpp24 Hpp16 Hpp8").
    iExists M7. iFrame "Hfile". iPureIntro. split; [exact Hra7|].
    repeat split.
    - rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. apply lookup_total_insert.
    - rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. apply lookup_total_insert.
    - rewrite /M7. rewrite lookup_total_insert.
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hcsp5. reflexivity.
    - rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Htp.
    - (* s2 (x18): never written by the epilogue chain nor by mycpu *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs2.
    - (* s3 (x19) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs3.
    - (* s4 (x20) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs4.
    - (* s5 (x21) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs5.
    - (* s6 (x22) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs6.
    - (* s7 (x23) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs7.
    - (* s8 (x24) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs8.
    - (* s9 (x25) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs9.
    - (* s10 (x26) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs10.
    - (* s11 (x27) *)
      rewrite /M7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /M2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs11.
  Qed.

  (* ============ the full push_off, entry (0x80000bc0) to caller return ============ *)
  Lemma wp_push_off (root_ppn : mword 44) (γ : gname) (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64))
      (noff intena_old : mword 32) (a0f : mword 64) (n : nat)
      :
    let sp0 := m !!! Regidx csp_rs1 in
    (* push_off's mstatus0-dependent register chain N2..N8 + storeval32 (which
       read [sstatus_read mstatus0]) are reconstructed inside the proof over the
       unbundled mstatus0; the statement stays mstatus0-free. *)
    let noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 noff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let noff_store := (autocast (T := mword) (subrange_vec_dec noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let a_noff := add_vec a0f (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_intena := add_vec a0f (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let caller_ret := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (6 ≤ n)%nat ->
    (* S-mode config facts + legalize are folded into [smode_config γ] below;
       the 4 mycpu a0f pins reduce to the single tp-only fact (po_mycpu_out_a0). *)
    eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false ->
    eq_vec (access_vec_dec caller_ret 0) ('b"0") = true ->
    mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) = a0f ->
    smode_config γ (DfracOwn 1) -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int (PO + 0x00) : mword 64) -∗ gpr_file m -∗
    (* push_off's whole 6-slot frame [sp0-48, sp0) as [stack_own sp0 n] (n>=6):
       slots 1/2/3 = saved ra/s0/s1 (a_r24/a_r16/a_r8), slot 4 = spd gap,
       slots 5/6 = mycpu's ra/s0. *)
    stack_own sp0 n -∗
    a_noff ↦₄ noff -∗
    a_intena ↦₄ intena_old -∗
    ( ∀ mfin,
      smode_config γ (DfracOwn 1) -∗
      tlb_inv root_ppn -∗
      pc_is caller_ret -∗
      gpr_file mfin -∗
      ⌜ callee_saved m mfin ⌝ -∗
      stack_own sp0 n -∗
      a_noff ↦₄ noff_store -∗
      a_intena ↦₄ (if eq_vec (sign_extend' 64 noff) zero_reg then (zeros' 32) else intena_old) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 noff_a5 noff_store a_noff a_intena caller_ret Hn Himm5 Hcret0 Ha0.
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (N0 := <[Regidx csp_rs1 := regval_into_reg spd]> m).
    set (N1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (N0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> N0).
    iIntros "Hsm Htlbinv #Htext Hpc Hfile Hframe Hnoff Hintena Hcont".
    (* peel the top 4 own slots as cells; keep mycpu's 2-slot frame as a
       [stack_own] slice the body threads directly. *)
    iDestruct (stack_own_split_1 sp0 6 n ltac:(lia) with "Hframe") as "[Htop Hdeep]".
    iDestruct (stack_own_split_1 sp0 4 6 ltac:(lia) with "Htop") as "[Hown Hstk]".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hown".
    iDestruct "Hown" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24".
    iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8) "Hr8".
    iDestruct "S4" as (vgap) "Hgap".
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8". iEval (rewrite Hspd4) in "Hstk".
    assert (Hcsp0 : N0 !!! Regidx csp_rs1 = spd) by (rewrite /N0; apply lookup_total_insert).
    (* ---- 0x00: c.addi sp,-32 ---- *)
    iPoseProof (poi_00 with "Htext") as "Hi00".
    iApply (wp_caddi_gpr_s root_ppn γ Φ (mword_of_int (PO + 0x00)) csp_rs1 (mword_of_int 32 : mword 6) m (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    assert (Hpp02 : add_vec_int (mword_of_int (PO + 0x00) : mword 64) 2 = mword_of_int (PO + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* ---- 0x02: c.sdsp ra,24(sp) ---- *)
    iPoseProof (poi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_ram_scfg root_ppn γ Φ (mword_of_int (PO + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              N0 vr24 (dq:=DfracOwn 1)
              with "Hsm Htlbinv Hpc Hfile Hi02 [Hr24] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr24". }
    iIntros "Hsm Htlbinv Hpc Hfile Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (PO + 0x02) : mword 64) 2 = mword_of_int (PO + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,16(sp) ---- *)
    iPoseProof (poi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_ram_scfg root_ppn γ Φ (mword_of_int (PO + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              N0 vr16 (dq:=DfracOwn 1)
              with "Hsm Htlbinv Hpc Hfile Hi04 [Hr16] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr16". }
    iIntros "Hsm Htlbinv Hpc Hfile Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (PO + 0x04) : mword 64) 2 = mword_of_int (PO + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.sdsp s1,8(sp) ---- *)
    iPoseProof (poi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_ram_scfg root_ppn γ Φ (mword_of_int (PO + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              N0 vr8 (dq:=DfracOwn 1)
              with "Hsm Htlbinv Hpc Hfile Hi06 [Hr8] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr8". }
    iIntros "Hsm Htlbinv Hpc Hfile Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (PO + 0x06) : mword 64) 2 = mword_of_int (PO + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iPoseProof (poi_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_gpr_s root_ppn γ Φ (mword_of_int (PO + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              N0 (dq:=DfracOwn 1)
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    assert (Hpp0a : add_vec_int (mword_of_int (PO + 0x08) : mword 64) 2 = mword_of_int (PO + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ---- 0x0a: csrrci a5,sstatus,2 ---- *)
    iPoseProof (poi_0a with "Htext") as "Hi0a".
    iApply (wp_csrrci_sstatus_scfg root_ppn γ Φ (mword_of_int (PO + 0x0a)) (mword_of_int 15 : mword 5)
              N1 (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hsm Htlbinv Hpc Hfileex".
    (* the sstatus read yields SOME [mstatus0] with SIE=0 (from the ghost); the
       [N2..N8] register chain + [storeval32] are built over that [mstatus0]. *)
    iDestruct "Hfileex" as (mstatus0) "[%HSIE Hfile]".
    set (N2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read mstatus0)]> N1).
    set (N3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (N2 !!! Regidx (mword_of_int 15 : mword 5)))]> N2).
    assert (HN3tp : N3 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (Hpp0e : add_vec_int (mword_of_int (PO + 0x0a) : mword 64) 4 = mword_of_int (PO + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* ---- 0x0e: c.mv s1,a5 ---- *)
    iPoseProof (poi_0e with "Htext") as "Hi0e".
    iApply (wp_cmv_gpr_s root_ppn γ Φ (mword_of_int (PO + 0x0e)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5)
              N2 (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi0e [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    assert (Hpp10 : add_vec_int (mword_of_int (PO + 0x0e) : mword 64) 2 = mword_of_int (PO + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* ---- 0x10: jal ra,mycpu (jimm=0xd06); a0 := &mycpu()[cpu] ---- *)
    assert (Hcsp3n : N3 !!! Regidx csp_rs1 = spd).
    { rewrite /N3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /N2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /N1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hcsp0. }
    assert (Hm0csp10 : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PO + 0x10) : mword 64) 4)]> N3) !!! Regidx csp_rs1 = spd)
      by (rewrite lookup_total_insert_ne; [ exact Hcsp3n | vm_compute; discriminate ]).
    iPoseProof (poi_10 with "Htext") as "Hi10".
    iApply (wp_call_mycpu_scfg_cs root_ppn γ Φ (mword_of_int (PO + 0x10)) (mword_of_int 0xd06 : mword 21) N3
 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              with "Hsm Htlbinv Htext Hpc Hfile Hi10 [Hstk] [-]").
    { iEval (rewrite Hm0csp10). iExact "Hstk". }
    iIntros (mo1) "Hsm Htlbinv Hpc Hfile %Hmo4 Hstk".
    set (N4 := mo1).
    destruct Hmo4 as [Hmo4cs Hmo4a0].
    destruct Hmo4cs as (Hcsp4 & Htp4 & Hs0_4 & Hs1_4 & Hs2_4 & Hs3_4 & Hs4_4 & Hs5_4 & Hs6_4 & Hs7_4 & Hs8_4 & Hs9_4 & Hs10_4 & Hs11_4).
    set (N5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noff)]> N4).
    assert (HN5tp : N5 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Htp4. exact HN3tp. }
    assert (Ha0_10 : N4 !!! Regidx (mword_of_int 10 : mword 5) = a0f).
    { rewrite Hmo4a0 HN3tp. exact Ha0. }
    iEval (rewrite Hm0csp10) in "Hstk".
    iEval (rewrite lookup_total_insert) in "Hpc".
    assert (Hpc14 : update_vec_dec (add_vec (add_vec_int (mword_of_int (PO + 0x10) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (PO + 0x14) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* ---- 0x14: c.lw a5,120(a0) : a5 := noff ---- *)
    assert (Hnoffaddr : N4 !!! Regidx (mword_of_int 10 : mword 5) = a0f) by (rewrite /N4; exact Ha0_10).
    iPoseProof (poi_14 with "Htext") as "Hi14".
    iApply (wp_clw_s_ram_scfg root_ppn γ Φ (mword_of_int (PO + 0x14)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 120 : mword 12) N4 noff
              (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi14 [Hnoff] [-]").
    { iEval (rewrite Hnoffaddr). iExact "Hnoff". }
    iIntros "Hsm Htlbinv Hpc Hfile Hnoff".
    assert (Hpp16 : add_vec_int (mword_of_int (PO + 0x14) : mword 64) 2 = mword_of_int (PO + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* ---- 0x16: c.beqz a5, 0x2c ---- *)
    assert (Ha5 : N5 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 noff) by (rewrite /N5; apply lookup_total_insert).
    assert (Hv1 : N0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /N0; rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (Hv8 : N0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /N0; rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (Hv9 : N0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /N0; rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (HcspN5 : N5 !!! Regidx csp_rs1 = spd).
    { rewrite /N5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hcsp4. exact Hcsp3n. }
    (* convert held memory to clean addresses/values (shared by both arms) *)
    iEval (rewrite Hnoffaddr) in "Hnoff".
    iEval (rewrite Hcsp0) in "Hr24". iEval (rewrite Hv1) in "Hr24".
    iEval (rewrite Hcsp0) in "Hr16". iEval (rewrite Hv8) in "Hr16".
    iEval (rewrite Hcsp0) in "Hr8". iEval (rewrite Hv9) in "Hr8".
    iPoseProof (poi_16 with "Htext") as "Hi16".
    destruct (eq_vec (sign_extend' 64 noff) zero_reg) eqn:Hcond.
    - (* ===== TAKEN arm: noff == 0 ===== *)
      iApply (wp_cbeqz_taken_s_zca_scfg root_ppn γ Φ (mword_of_int (PO + 0x16)) (mword_of_int 11 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) N5 (dq:=DfracOwn 1)
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rewrite Ha5; exact Hcond)
                ltac:(vm_compute; reflexivity)
                with "Hsm Htlbinv Hpc Hfile Hi16 [-]").
      iIntros "Hsm Htlbinv Hpc Hfile".
      assert (Htgt2c : add_vec (mword_of_int (PO + 0x16) : mword 64)
                 (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")))) = mword_of_int (PO + 0x2c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt2c) in "Hpc".
      (* ---- 0x2c: jal ra,mycpu (jimm=0xcea) ---- *)
      assert (Hm0csp2c : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PO + 0x2c) : mword 64) 4)]> N5) !!! Regidx csp_rs1 = spd)
        by (rewrite lookup_total_insert_ne; [ exact HcspN5 | vm_compute; discriminate ]).
      iPoseProof (poi_2c with "Htext") as "Hi2c".
      iApply (wp_call_mycpu_scfg_cs root_ppn γ Φ (mword_of_int (PO + 0x2c)) (mword_of_int 0xcea : mword 21) N5
 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
                with "Hsm Htlbinv Htext Hpc Hfile Hi2c [Hstk] [-]").
      { iEval (rewrite Hm0csp2c). iExact "Hstk". }
      iIntros (mo2) "Hsm Htlbinv Hpc Hfile %Hmo6 Hstk".
      set (N6 := mo2).
      destruct Hmo6 as [Hmo6cs Hmo6a0].
      destruct Hmo6cs as (Hcsp6 & Htp6 & Hs0_6 & Hs1_6 & Hs2_6 & Hs3_6 & Hs4_6 & Hs5_6 & Hs6_6 & Hs7_6 & Hs8_6 & Hs9_6 & Hs10_6 & Hs11_6).
      set (N7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (shift_bits_right (N6 !!! Regidx (mword_of_int 9 : mword 5))
             (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))]> N6).
      set (N8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (N7 !!! Regidx (mword_of_int 15 : mword 5))
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> N7).
      set (storeval32 := (autocast (T := mword)
          (subrange_vec_dec (N8 !!! Regidx (mword_of_int 15 : mword 5)) (Z.sub (Z.mul 4 8) 1) 0) : mword 32)).
      assert (HN8tp : N8 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
      { rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Htp6. exact HN5tp. }
      assert (Ha0_2c : N6 !!! Regidx (mword_of_int 10 : mword 5) = a0f).
      { rewrite Hmo6a0 HN5tp. exact Ha0. }
      assert (Ha0_18t : mycpu_ret (N8 !!! Regidx (mword_of_int 4 : mword 5)) = a0f)
        by (rewrite HN8tp; exact Ha0).
      assert (Hsv32 : storeval32 = zeros' 32).
      { rewrite /storeval32 /N8 lookup_total_insert /N7 lookup_total_insert.
        rewrite Hs1_6 /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hs1_4 /N3 lookup_total_insert /N2 lookup_total_insert.
        apply po_storeval32_zero. exact HSIE. }
      iEval (rewrite Hm0csp2c) in "Hstk".
      iEval (rewrite lookup_total_insert) in "Hpc".
      assert (Hpc30 : update_vec_dec (add_vec (add_vec_int (mword_of_int (PO + 0x2c) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                      = (mword_of_int (PO + 0x30) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc30) in "Hpc".
      (* ---- 0x30: srli a5,s1,1 ---- *)
      iPoseProof (poi_30 with "Htext") as "Hi30".
      iApply (wp_srli4_s_scfg root_ppn γ Φ (mword_of_int (PO + 0x30)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 1 : mword 6) N6 (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
                with "Hsm Htlbinv Hpc Hfile Hi30 [-]").
      iIntros "Hsm Htlbinv Hpc Hfile".
      assert (Hpc34 : add_vec_int (mword_of_int (PO + 0x30) : mword 64) 4 = mword_of_int (PO + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc34) in "Hpc".
      (* ---- 0x34: andi a5,a5,1 ---- *)
      iPoseProof (poi_34 with "Htext") as "Hi34".
      iApply (wp_candi_s_scfg root_ppn γ Φ (mword_of_int (PO + 0x34)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6)
                N7 (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
                with "Hsm Htlbinv Hpc Hfile Hi34 [-]").
      iIntros "Hsm Htlbinv Hpc Hfile".
      assert (Hpc36 : add_vec_int (mword_of_int (PO + 0x34) : mword 64) 2 = mword_of_int (PO + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc36) in "Hpc".
      (* ---- 0x36: c.sw a5,124(a0) : store intena ---- *)
      assert (Hintaddr : N8 !!! Regidx (mword_of_int 10 : mword 5) = a0f).
      { rewrite /N8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /N7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Ha0_2c. }
      iPoseProof (poi_36 with "Htext") as "Hi36".
      iApply (wp_csw_s_ram_scfg root_ppn γ Φ (mword_of_int (PO + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
                (mword_of_int 124 : mword 12) N8 intena_old (dq:=DfracOwn 1)

                with "Hsm Htlbinv Hpc Hfile Hi36 [Hintena] [-]").
      { iEval (rewrite Hintaddr). iExact "Hintena". }
      iIntros "Hsm Htlbinv Hpc Hfile Hintena".
      iEval (rewrite Hintaddr) in "Hintena".
      assert (Hpc38 : add_vec_int (mword_of_int (PO + 0x36) : mword 64) 2 = mword_of_int (PO + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc38) in "Hpc".
      (* ---- 0x38: c.j 0xbd8 ---- *)
      iPoseProof (poi_38 with "Htext") as "Hi38".
      iApply (wp_cj_s_scfg root_ppn γ Φ (mword_of_int (PO + 0x38)) (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")))
                N8 (dq:=DfracOwn 1)
 ltac:(vm_compute; reflexivity)
                with "Hsm Htlbinv Hpc Hfile Hi38 [-]").
      iIntros "Hsm Htlbinv Hpc Hfile".
      assert (Htgt18t : add_vec (mword_of_int (PO + 0x38) : mword 64)
                 (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")))) = mword_of_int (PO + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt18t) in "Hpc".
      assert (HcspN8 : N8 !!! Regidx csp_rs1 = spd).
      { rewrite /N8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /N7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hcsp6. exact HcspN5. }
      (* ---- apply the suffix with ms = N8 ---- *)
      iApply (wp_push_off_suffix root_ppn γ Φ N8 noff
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5)) (m !!! Regidx (mword_of_int 9 : mword 5))
 Hcret0
                with "Hsm Htlbinv Htext Hpc Hfile [Hstk] [Hnoff] [Hr24] [Hr16] [Hr8] [-]").
      { iEval (rewrite HcspN8). iExact "Hstk". }
      { iEval (rewrite Ha0_18t). iExact "Hnoff". }
      { iEval (rewrite HcspN8). iExact "Hr24". }
      { iEval (rewrite HcspN8). iExact "Hr16". }
      { iEval (rewrite HcspN8). iExact "Hr8". }
      iIntros "Hsm Htlbinv Hpc Hmfin Hstk Hnoff Hr24 Hr16 Hr8".
      iEval (rewrite HcspN8) in "Hstk".
      iEval (rewrite Ha0_18t) in "Hnoff".
      iEval (rewrite HcspN8) in "Hr24". iEval (rewrite HcspN8) in "Hr16". iEval (rewrite HcspN8) in "Hr8".
      iDestruct "Hmfin" as (mfin) "[Hmf %Hp]".
      destruct Hp as (Hra & Hs0 & Hs1 & Hsp & Htp & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
      iEval (rewrite Hb1) in "Hr24". iEval (rewrite Hb2) in "Hr16".
      iEval (rewrite Hb3) in "Hr8". iEval (rewrite -Hspd4) in "Hstk".
      iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hown".
      { rewrite stack_own_slots. cbn [seq]. iSplitL "Hr24"; [by iExists _|].
        iSplitL "Hr16"; [by iExists _|]. iSplitL "Hr8"; [by iExists _|].
        iSplitL "Hgap"; [by iExists _|]. done. }
      iDestruct (stack_own_split_2 sp0 4 6 ltac:(lia) with "[$Hown $Hstk]") as "Htopf".
      iDestruct (stack_own_split_2 sp0 6 n ltac:(lia) with "[$Htopf $Hdeep]") as "Hstkf".
      iApply ("Hcont" $! mfin with "Hsm Htlbinv Hpc Hmf [%] Hstkf Hnoff [Hintena]").
      { unfold callee_saved. repeat split.
        - (* sp *)
          rewrite Hsp HcspN8 /spd /sp0 po_addv_assoc.
          assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                                (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite HAB. apply avi0.
        - (* tp *)
          rewrite Htp.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Htp6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Htp4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s0 *) exact Hs0.
        - (* s1 *) exact Hs1.
        - (* s2 *)
          rewrite Hs2.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs2_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs2_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s3 *)
          rewrite Hs3.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs3_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs3_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s4 *)
          rewrite Hs4.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs4_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs4_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s5 *)
          rewrite Hs5.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs5_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs5_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s6 *)
          rewrite Hs6.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs6_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs6_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s7 *)
          rewrite Hs7.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs7_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs7_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s8 *)
          rewrite Hs8.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs8_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs8_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s9 *)
          rewrite Hs9.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs9_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs9_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s10 *)
          rewrite Hs10.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs10_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs10_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s11 *)
          rewrite Hs11.
          rewrite /N8 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N7 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs11_6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs11_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
      { first [ iExact "Hintena" | (iEval (rewrite -Hsv32); iExact "Hintena") ]. }
    - (* ===== FALL arm: noff <> 0 ===== *)
      iApply (wp_cbeqz_fall_s root_ppn γ Φ (mword_of_int (PO + 0x16)) (mword_of_int 11 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) N5 (dq:=DfracOwn 1)
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rewrite Ha5; exact Hcond)
                with "Hsm Htlbinv Hpc Hfile Hi16 [-]").
      iIntros "Hsm Htlbinv Hpc Hfile".
      assert (Hpc18 : add_vec_int (mword_of_int (PO + 0x16) : mword 64) 2 = mword_of_int (PO + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc18) in "Hpc".
      assert (Ha0_18f : mycpu_ret (N5 !!! Regidx (mword_of_int 4 : mword 5)) = a0f)
        by (rewrite HN5tp; exact Ha0).
      (* ---- apply the suffix with ms = N5 ---- *)
      iApply (wp_push_off_suffix root_ppn γ Φ N5 noff
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5)) (m !!! Regidx (mword_of_int 9 : mword 5))
 Hcret0
                with "Hsm Htlbinv Htext Hpc Hfile [Hstk] [Hnoff] [Hr24] [Hr16] [Hr8] [-]").
      { iEval (rewrite HcspN5). iExact "Hstk". }
      { iEval (rewrite Ha0_18f). iExact "Hnoff". }
      { iEval (rewrite HcspN5). iExact "Hr24". }
      { iEval (rewrite HcspN5). iExact "Hr16". }
      { iEval (rewrite HcspN5). iExact "Hr8". }
      iIntros "Hsm Htlbinv Hpc Hmfin Hstk Hnoff Hr24 Hr16 Hr8".
      iEval (rewrite HcspN5) in "Hstk".
      iEval (rewrite Ha0_18f) in "Hnoff".
      iEval (rewrite HcspN5) in "Hr24". iEval (rewrite HcspN5) in "Hr16". iEval (rewrite HcspN5) in "Hr8".
      iDestruct "Hmfin" as (mfin) "[Hmf %Hp]".
      destruct Hp as (Hra & Hs0 & Hs1 & Hsp & Htp & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11).
      iEval (rewrite Hb1) in "Hr24". iEval (rewrite Hb2) in "Hr16".
      iEval (rewrite Hb3) in "Hr8". iEval (rewrite -Hspd4) in "Hstk".
      iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hown".
      { rewrite stack_own_slots. cbn [seq]. iSplitL "Hr24"; [by iExists _|].
        iSplitL "Hr16"; [by iExists _|]. iSplitL "Hr8"; [by iExists _|].
        iSplitL "Hgap"; [by iExists _|]. done. }
      iDestruct (stack_own_split_2 sp0 4 6 ltac:(lia) with "[$Hown $Hstk]") as "Htopf".
      iDestruct (stack_own_split_2 sp0 6 n ltac:(lia) with "[$Htopf $Hdeep]") as "Hstkf".
      iApply ("Hcont" $! mfin with "Hsm Htlbinv Hpc Hmf [%] Hstkf Hnoff [Hintena]").
      { unfold callee_saved. repeat split.
        - (* sp *)
          rewrite Hsp HcspN5 /spd /sp0 po_addv_assoc.
          assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                                (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite HAB. apply avi0.
        - (* tp *)
          rewrite Htp.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Htp4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s0 *) exact Hs0.
        - (* s1 *) exact Hs1.
        - (* s2 *)
          rewrite Hs2.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs2_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s3 *)
          rewrite Hs3.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs3_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s4 *)
          rewrite Hs4.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs4_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s5 *)
          rewrite Hs5.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs5_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s6 *)
          rewrite Hs6.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs6_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s7 *)
          rewrite Hs7.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs7_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s8 *)
          rewrite Hs8.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs8_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s9 *)
          rewrite Hs9.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs9_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s10 *)
          rewrite Hs10.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs10_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity.
        - (* s11 *)
          rewrite Hs11.
          rewrite /N5 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite Hs11_4.
          rewrite /N3 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N2 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N1 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /N0 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
      { first [ iExact "Hintena" | (iEval (rewrite -Hsv32); iExact "Hintena") ]. }
  Qed.



End WpPushOffTop.
