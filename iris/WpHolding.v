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
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode WpLeafCommon KernelText.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Export WpSmodeLoad WpSmodeStore WpSmodeBtype.
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

(* [hexec_bnez] moved to WpMmodeLeafBase as [exec_execute_C_BNEZ] (shared
   compressed-BNEZ exec fact; also used by pop_off/acquire retry loops). *)

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
Lemma hdec_jal_mycpu s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x52d000ef : mword 32)) s
  = Some (JAL (mword_of_int 0xd2c : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; h_dbase s Hpriv ]. Qed.

(* +0x1a  0x40a48533  sub a0,s1,a0 *)
Lemma hdec_sub s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40a48533 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 9), Regidx (mword_of_int 10), SUB), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; h_dbase s Hpriv ]. Qed.

(* +0x1e  0x00153513  seqz a0,a0 (sltiu a0,a0,1) *)
Lemma hdec_seqz s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00153513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLTIU), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; h_dbase s Hpriv ]. Qed.

(* gpr_sub_val/gpr_sltiu_val + exec_execute_RTYPE_SUB_gpr/ITYPE_SLTIU_gpr relocated to WpMmodeLeafBase.v *)

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

Section WpHolding.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* c.bnez rs NOT taken (rs = 0): fall through to pc+2.  Mirrors          *)
  (* WpMemsetS.wp_cbeqz_fall_s_config with BEQ -> BNE.                     *)
  (* ------------------------------------------------------------------- *)


  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the four fast-path instructions.                    *)
  (* ------------------------------------------------------------------- *)
  Lemma hi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x0) : mword 64) true
      (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (KernelSyms.holding + 0x0)%Z (mword_of_int 0x411c : mword 16)
    (mword_of_int (KernelSyms.holding + 0x0) : mword 64)
    (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) hdec_lw hexec_lw. Qed.

  Lemma hi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x2) : mword 64) true
      (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (KernelSyms.holding + 0x2)%Z (mword_of_int 0xe399 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x2) : mword 64)
    (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) hdec_bnez exec_execute_C_BNEZ. Qed.

  Lemma hi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x4) : mword 64) true
      (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KernelSyms.holding + 0x4)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x4) : mword 64)
    (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) hdec_li exec_execute_C_LI. Qed.

  Lemma hi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x6) : mword 64) true
      (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.holding + 0x6)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x6) : mword 64)
    (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) podec_2a exec_execute_C_JR. Qed.


  Lemma his_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x08) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.holding + 0x08)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x08) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) podec_00 exec_execute_C_ADDI. Qed.

  Lemma his_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.holding + 0x0a)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) podec_02 exec_execute_C_SDSP. Qed.

  Lemma his_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.holding + 0x0c)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) podec_04 exec_execute_C_SDSP. Qed.

  Lemma his_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.holding + 0x0e)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) podec_06 exec_execute_C_SDSP. Qed.

  Lemma his_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x10) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.holding + 0x10)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x10) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) podec_08 exec_execute_C_ADDI4SPN. Qed.

  Lemma his_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x12) : mword 64) true (LOAD (mword_of_int 16, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc (KernelSyms.holding + 0x12)%Z (mword_of_int 0x691c : mword 16)
    (mword_of_int (KernelSyms.holding + 0x12) : mword 64) (LOAD (mword_of_int 16, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)) hdec_ld hexec_ld. Qed.

  Lemma his_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x14) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.holding + 0x14)%Z (mword_of_int 0x84be : mword 16)
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
  Proof. mk_rvc (KernelSyms.holding + 0x22)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) podec_22 exec_execute_C_LDSP. Qed.

  Lemma his_24 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x24) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.holding + 0x24)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x24) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) podec_24 exec_execute_C_LDSP. Qed.

  Lemma his_26 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x26) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.holding + 0x26)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x26) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) podec_26 exec_execute_C_LDSP. Qed.

  Lemma his_28 : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x28) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.holding + 0x28)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x28) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) podec_28 exec_execute_C_ADDI16SP. Qed.

  Lemma his_2a : kernel_text -∗ instr (mword_of_int (KernelSyms.holding + 0x2a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.holding + 0x2a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.holding + 0x2a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) podec_2a exec_execute_C_JR. Qed.

End WpHolding.
