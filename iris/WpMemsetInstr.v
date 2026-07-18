(* WpMemsetInstr.v -- discharge the instruction DECODINGS for all 16 memset
   instructions (0x80000ccc .. 0x80000cf0) from [kernel_text], then a corollary
   [wp_memset_s_full_kt] of [wp_memset_s_full] that assumes only [kernel_text]
   instead of the 16 [instr]/decode premises.

   The eight standard prologue/epilogue instructions (c.addi16sp / c.sdsp /
   c.ldsp / c.jr) share their byte patterns with WpTimerinit's, so their decode
   lemmas are reused verbatim; the other eight (c.mv / c.slli / c.srli / c.beqz /
   c.addi a5,1 and the three base add/sb/bne) get fresh decode lemmas here. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode WpLeafCommon.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SRegime.
Require Import SmodeCore KernelText WpMemsetS.
Require Import StackOwn.
Require Import WpRvcBridge.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Import CalleeSaved.
Local Open Scope Z_scope.
Require Import PtAdBits PtTree PtTreeAdue KptTree SmodeCorePt.
Require Import WpSmodePtLeaves WpSmodePtAlu WpSmodePtBtype WpSmodePtCtl.
Require Import WpSmodePtMem WpSmodePtMemWrap WpSmodePtLock WpSmodePtUart.
Import Defs.

(* ===================================================================== *)
(* Decode templates.                                                      *)
(* ===================================================================== *)
Local Ltac m_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac m_close1 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; m_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

Local Ltac m_close0 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; m_ast
  | apply (exec_currentlyEnabled_Zca s HmisaC) ].

(* The eight 16-byte-frame prologue/epilogue decodes ([mdec_ccc]..[mdec_cf0],
   c.addi sp / c.sdsp / c.addi4spn / c.ldsp / c.ret) live in KernelRvcDecode.v,
   shared with the other functions that use this frame. *)

(* ---- the five fresh RVC decodes ---- *)
(* cd6: 0x87aa -> c.mv a5,a0 *)
Lemma mdec_cd6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x87aa : mword 16)) s = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 10)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* cd8: 0x1602 -> c.slli a2,32 *)
Lemma mdec_cd8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1602 : mword 16)) s = Some (C_SLLI (mword_of_int 32, Regidx (mword_of_int 12)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* cda: 0x9201 -> c.srli a2,32 *)
Lemma mdec_cda s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9201 : mword 16)) s = Some (C_SRLI (mword_of_int 32, Cregidx (mword_of_int 4)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* cd4: 0xca19 -> c.beqz a2,cea *)
Lemma mdec_cd4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xca19 : mword 16)) s = Some (C_BEQZ (mword_of_int 11, Cregidx (mword_of_int 4)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* ce4: 0x0785 -> c.addi a5,1 *)
Lemma mdec_ce4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0785 : mword 16)) s = Some (C_ADDI (mword_of_int 1, Regidx (mword_of_int 15)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* ---- the three base decodes (one-shot decode_any) ---- *)
(* cdc: 0x00a60733 -> add a4,a2,a0 *)
Lemma mdec_cdc s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00a60733 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* ce0: 0x00b78023 -> sb a1,0(a5) *)
Lemma mdec_ce0 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00b78023 : mword 32)) s
  = Some (STORE (mword_of_int 0, Regidx (mword_of_int 11), Regidx (mword_of_int 15), 1), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* ce6: 0xfee79de3 -> bne a5,a4,ce0 *)
Lemma mdec_ce6 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfee79de3 : mword 32)) s
  = Some (BTYPE (mword_of_int 0x1ffa, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* ===================================================================== *)
(* [instr] constructors from [kernel_text].                              *)
(* ===================================================================== *)
Section WpMemsetInstr.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* [mk_rvc] targets the ExecuteAs-EXPANDED base instruction:
     [instr pc true base], where [decname] decodes the compressed form i0 and
     [expname] is i0's [exec_execute_C_*] ExecuteAs-expansion into [base].
     Addresses are given as [KernelSyms.memset + offset]; the [mdec_*] decode
     lemmas are keyed by instruction BITS (address-independent), so their names
     carry a low-byte address that need not match the current image. *)

  (* +0x00  c.addi16sp sp,-16  ->  addi sp,sp,-16 *)
  Lemma minstr_cba : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.memset + 0x00)%Z (mword_of_int 0x1141 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.

  (* +0x02  c.sdsp ra,8(sp)  ->  sd ra,8(sp) *)
  Lemma minstr_cbc : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.memset + 0x02)%Z (mword_of_int 0xe406 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.

  (* +0x04  c.sdsp s0,0(sp)  ->  sd s0,0(sp) *)
  Lemma minstr_cbe : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.memset + 0x04)%Z (mword_of_int 0xe022 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.

  (* +0x06  c.addi4spn s0,sp,16  ->  addi s0,sp,16 *)
  Lemma minstr_cc0 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.memset + 0x06)%Z (mword_of_int 0x0800 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.

  (* +0x08  c.beqz a2,+0x1e  ->  beq a2,x0,+0x1e *)
  Lemma minstr_cc2 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x08) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)).
  Proof. mk_rvc (KernelSyms.memset + 0x08)%Z (mword_of_int 0xca19 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x08) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)) mdec_cd4 exec_execute_C_BEQZ. Qed.

  (* +0x0a  c.mv a5,a0  ->  add a5,x0,a0 *)
  Lemma minstr_cc4 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (KernelSyms.memset + 0x0a)%Z (mword_of_int 0x87aa : mword 16)
           (mword_of_int (KernelSyms.memset + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 15), ADD)) mdec_cd6 exec_execute_C_MV. Qed.

  (* +0x0c  c.slli a2,32  ->  slli a2,a2,32 *)
  Lemma minstr_cc6 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x0c) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)).
  Proof. mk_rvc (KernelSyms.memset + 0x0c)%Z (mword_of_int 0x1602 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x0c) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)) mdec_cd8 exec_execute_C_SLLI. Qed.

  (* +0x0e  c.srli a2,32  ->  srli a2,a2,32 *)
  Lemma minstr_cc8 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x0e) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, creg2reg_idx (Cregidx (mword_of_int 4)), creg2reg_idx (Cregidx (mword_of_int 4)), SRLI)).
  Proof. mk_rvc (KernelSyms.memset + 0x0e)%Z (mword_of_int 0x9201 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x0e) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, creg2reg_idx (Cregidx (mword_of_int 4)), creg2reg_idx (Cregidx (mword_of_int 4)), SRLI)) mdec_cda exec_execute_C_SRLI. Qed.

  (* +0x10  add a4,a2,a0        (base, 2-aligned) *)
  Lemma minstr_cca : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x10) : mword 64) false (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD)).
  Proof. mk_base (KernelSyms.memset + 0x10)%Z (mword_of_int 0x00a60733 : mword 32)
           (mword_of_int (KernelSyms.memset + 0x10) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD)) mdec_cdc. Qed.

  (* +0x14  sb a1,0(a5)  [LOOP head]  (base, 2-aligned) *)
  Lemma minstr_cce : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x14) : mword 64) false (STORE (mword_of_int 0, Regidx (mword_of_int 11), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (KernelSyms.memset + 0x14)%Z (mword_of_int 0x00b78023 : mword 32)
           (mword_of_int (KernelSyms.memset + 0x14) : mword 64) (STORE (mword_of_int 0, Regidx (mword_of_int 11), Regidx (mword_of_int 15), 1)) mdec_ce0. Qed.

  (* +0x18  c.addi a5,1  ->  addi a5,a5,1 *)
  Lemma minstr_cd2 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x18) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (KernelSyms.memset + 0x18)%Z (mword_of_int 0x0785 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) mdec_ce4 exec_execute_C_ADDI. Qed.

  (* +0x1a  bne a5,a4,+0x14     (base, 4-aligned) *)
  Lemma minstr_cd4 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x1a) : mword 64) false (BTYPE (mword_of_int 0x1ffa, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (KernelSyms.memset + 0x1a)%Z (mword_of_int 0xfee79de3 : mword 32)
           (mword_of_int (KernelSyms.memset + 0x1a) : mword 64) (BTYPE (mword_of_int 0x1ffa, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE)) mdec_ce6. Qed.

  (* +0x1e  c.ldsp ra,8(sp)  ->  ld ra,8(sp) *)
  Lemma minstr_cd8 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.memset + 0x1e)%Z (mword_of_int 0x60a2 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.

  (* +0x20  c.ldsp s0,0(sp)  ->  ld s0,0(sp) *)
  Lemma minstr_cda : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x20) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.memset + 0x20)%Z (mword_of_int 0x6402 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x20) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.

  (* +0x22  c.addi16sp sp,16  ->  addi sp,sp,16 *)
  Lemma minstr_cdc : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x22) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.memset + 0x22)%Z (mword_of_int 0x0141 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x22) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.

  (* +0x24  c.jr ra  (ret)  ->  jalr x0,0(ra) *)
  Lemma minstr_cde : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x24) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.memset + 0x24)%Z (mword_of_int 0x8082 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x24) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE: [wp_memset_s_full_kt] — the whole-function memset WP,   *)
  (*  with the sixteen instruction decodings discharged from [kernel_text]  *)
  (*  and the 2-slot save frame carried as a single [stack_own sp0 n]       *)
  (*  (n >= 2).  The Sv39 superpage-identity geometry (svpn := svpn_of a8)  *)
  (*  is derived at the [wp_sb_s_pt] leaf, so no svpn side conditions appear.   *)
  (* =================================================================== *)

  Lemma wp_memset_s_full_kt_r (R : s_regime) (Φ : mval -> iProp Σ)
      (m0 : gmap regidx (mword 64)) (N : nat) (wval_add : mword 64)
      (olds : nat -> bv 8) (n : nat)
      (γ : gname) {dq : dfrac} :
    let ra_idx : mword 5 := mword_of_int 1 in
    let s0_idx : mword 5 := mword_of_int 8 in
    let a0_idx : mword 5 := mword_of_int 10 in
    let a1_idx : mword 5 := mword_of_int 11 in
    let a2_idx : mword 5 := mword_of_int 12 in
    let a5_idx : mword 5 := mword_of_int 15 in
    let pcE := mword_of_int KernelSyms.memset in
    let imm_entry : mword 6 := mword_of_int 48 in
    let shamt_l : mword 6 := mword_of_int 32 in
    let shamt_r : mword 6 := mword_of_int 32 in
    let nzimm_s0 : mword 8 := mword_of_int 4 in
    let sp0 := m0 !!! Regidx csp_rs1 in
    let sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)) in
    let ra0 := m0 !!! Regidx ra_idx in
    let p := m0 !!! Regidx a0_idx in
    let e := wval_add in
    let cval := m0 !!! Regidx a1_idx in
    let m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0 in
    let m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1 in
    let m3 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2 in
    let m4 := <[Regidx a2_idx := regval_into_reg (shift_bits_left (m3 !!! Regidx a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3 in
    let m5 := <[Regidx a2_idx := regval_into_reg (shift_bits_right (m4 !!! Regidx a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4 in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    let cbyte := nth_byte (autocast (T := mword) (subrange_vec_dec cval (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 in
    (2 <= n)%nat ->
    (* the ADD computing the loop end pointer [a4 := a2 + a0 = wval_add] *)
    add_vec (m5 !!! Regidx a2_idx) (m5 !!! Regidx a0_idx) = wval_add ->
    (* the entry [beqz a2] is taken exactly when the byte count [N] is zero:
       count register is zero iff N = 0 (a 0-byte memset skips the loop) *)
    eq_vec (m0 !!! Regidx a2_idx) zero_reg = Nat.eqb N 0 ->
    (* caller's return target's low bit is clear (2-aligned Zca return) *)
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    (* the end pointer couples to the buffer: [wval_add = ms_addr p N] *)
    (forall j : nat, (j < N)%nat -> neq_vec (ms_addr p (S j)) e = negb (Nat.eqb (S j) N)) ->
    smode_config γ dq -∗
    sr_inv R -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m0 -∗
    stack_own sp0 n -∗
    ([∗ list] j ∈ seq 0 N, (ms_pa (ms_addr p j)) ↦ₘ olds j) -∗
    ( ∀ mfin,
      smode_config γ dq -∗
      sr_inv R -∗
      pc_is ret_tgt -∗
      stack_own sp0 n -∗
      ([∗ list] j ∈ seq 0 N, (ms_pa (ms_addr p j)) ↦ₘ cbyte) -∗
      gpr_file mfin -∗
      ⌜ callee_saved m0 mfin ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ra_idx s0_idx a0_idx a1_idx a2_idx a5_idx pcE imm_entry shamt_l shamt_r nzimm_s0 sp0 sp' ra0 p e cval m1 m2 m3 m4 m5 ret_tgt cbyte Hn Hvalue_add Hcount0 Hret0 Hcmp.
    set (a4_idx := (mword_of_int 14 : mword 5)).
    set (pc0L := (mword_of_int (KernelSyms.memset + 0x14) : mword 64)).
    set (pcLS := (mword_of_int (KernelSyms.memset + 0x1e) : mword 64)).
    set (imm_dealloc := (mword_of_int 16 : mword 6)).
    set (imm8_beqz := (mword_of_int 11 : mword 8)).
    set (imm_bne := (mword_of_int 0x1ffa : mword 13)).
    set (s00 := m0 !!! Regidx s0_idx).
    set (m6 := <[Regidx a4_idx := regval_into_reg wval_add]> m5).
    pose proof (add_vec_frame_cancel) as Hframe.
    iIntros "Hsm Htlbinv
             #Htext Hpc Hfile Hstk Hbuf Hcont".
    (* peel the 2-slot save frame [sp0-16, sp0), lend the deeper region *)
    iDestruct (stack_own_split_1 sp0 2 n ltac:(lia) with "Hstk") as "[Htop Hdeep]".
    iDestruct (stack_own_2_elim with "Htop") as (vra vs0) "[Hbra Hbs0]".
    assert (Hb1 : add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hbra". iEval (rewrite -Hb2) in "Hbs0".
    (* split on the byte count: N = 0 skips the loop (the entry beqz is taken). *)
    destruct N as [| N'].
    { (* ===== N = 0: zero-byte memset; the entry c.beqz is taken ===== *)
      iPoseProof (minstr_cba with "Htext") as "Hi0".
      iPoseProof (minstr_cbc with "Htext") as "Hi2".
      iPoseProof (minstr_cbe with "Htext") as "Hi4".
      iPoseProof (minstr_cc0 with "Htext") as "Hi6".
      iPoseProof (minstr_cc2 with "Htext") as "Hi8".
      iPoseProof (minstr_cd8 with "Htext") as "HiL0".
      iPoseProof (minstr_cda with "Htext") as "HiL2".
      iPoseProof (minstr_cdc with "Htext") as "HiL4".
      iPoseProof (minstr_cde with "Htext") as "HiL6".
      (* prologue (0xccc..0xcd2) + taken c.beqz -> epilogue entry, map m2 *)
      iApply (wp_memset_empty_r R Φ m0 imm_entry nzimm_s0 imm8_beqz vra vs0
                γ (dq:=dq)

                ltac:(rewrite Hcount0; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hsm Htlbinv Hpc Hfile Hi0 Hi2 Hi4 Hi6 Hi8 Hbra Hbs0 [-]").
      iIntros "Hsm Htlbinv Hpc Hfile Hbra Hbs0".
      (* epilogue: restore ra/s0, dealloc frame, ret *)
      assert (Hsuf_sp0 : m2 !!! Regidx csp_rs1 = sp')
        by (unfold m2, m1; rewrite lookup_total_insert_ne; [ rewrite lookup_total_insert; reflexivity | vm_compute; discriminate ]).
      assert (Hsuf_ra0 : m2 !!! Regidx ra_idx = ra0).
      { unfold m2, m1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        unfold ra0; reflexivity. }
      iApply (wp_memset_suffix_r R Φ sp' ra0 s00 ra_idx s0_idx imm_dealloc m2
                γ (dq:=dq)(dqm:=DfracOwn 1)
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hsuf_sp0 Hsuf_ra0
                Hret0
                with "Hsm Htlbinv Hpc Hfile HiL0 HiL2 HiL4 HiL6 Hbra Hbs0 [-]").
      iIntros "Hsm Htlbinv Hpc Hbra Hbs0 Hmfin".
      iDestruct "Hmfin" as (mfin) "[Hfile %Hpins]".
      destruct Hpins as (Hpra & Hps0 & Hpcsp & Hpres).
      (* rebundle the restored 2-slot frame back to [stack_own sp0 n] *)
      iEval (rewrite Hb1) in "Hbra". iEval (rewrite Hb2) in "Hbs0".
      iDestruct (stack_own_2_intro with "Hbra Hbs0") as "Htop".
      iDestruct (stack_own_split_2 sp0 2 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
      iApply ("Hcont" $! mfin with "Hsm Htlbinv Hpc Hstk Hbuf Hfile [%]").
      (* callee_saved: only sp/s0 moved; every other reg passes straight through m2 = m0 *)
      assert (Hcatch : forall r : regidx,
                r <> Regidx ra_idx -> r <> Regidx s0_idx -> r <> Regidx csp_rs1 ->
                mfin !!! r = m0 !!! r).
      { intros r Hra Hs0 Hcsp.
        rewrite (Hpres r Hra Hs0 Hcsp).
        unfold m2, m1.
        rewrite lookup_total_insert_ne; [| exact (not_eq_sym Hs0)].
        rewrite lookup_total_insert_ne; [| exact (not_eq_sym Hcsp)].
        reflexivity. }
      unfold callee_saved. repeat split.
      - (* x2 sp: balanced frame *) rewrite Hpcsp. unfold sp'. apply Hframe.
      - (* x4 tp *) apply Hcatch; vm_compute; discriminate.
      - (* x8 s0 *) exact Hps0.
      - (* x9 s1 *) apply Hcatch; vm_compute; discriminate.
      - (* x18 s2 *) apply Hcatch; vm_compute; discriminate.
      - (* x19 s3 *) apply Hcatch; vm_compute; discriminate.
      - (* x20 s4 *) apply Hcatch; vm_compute; discriminate.
      - (* x21 s5 *) apply Hcatch; vm_compute; discriminate.
      - (* x22 s6 *) apply Hcatch; vm_compute; discriminate.
      - (* x23 s7 *) apply Hcatch; vm_compute; discriminate.
      - (* x24 s8 *) apply Hcatch; vm_compute; discriminate.
      - (* x25 s9 *) apply Hcatch; vm_compute; discriminate.
      - (* x26 s10 *) apply Hcatch; vm_compute; discriminate.
      - (* x27 s11 *) apply Hcatch; vm_compute; discriminate. }
    (* ===== N = S N': at least one byte; run the loop ===== *)
    assert (Hn0 : eq_vec (m0 !!! Regidx a2_idx) zero_reg = false)
      by (rewrite Hcount0; reflexivity).
    (* derive the thirteen prefix/suffix instr resources from the text image *)
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
    pose proof minstr_cce as Hext0.
    pose proof minstr_cd2 as Hext4.
    pose proof minstr_cd4 as Hext6.
    assert (Hcur : m6 !!! Regidx a5_idx = ms_addr p 0).
    { unfold m6, m5, m4, m3, m2, m1.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert.
      unfold regval_into_reg. rewrite add_vec_zero_l.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold ms_addr, p. change (Z.of_nat 0) with 0%Z. symmetry. exact (RiscvExtras.avi0 (m0 !!! Regidx a0_idx)). }
    assert (Hm4 : m6 !!! Regidx a4_idx = e)
      by (unfold m6, e; rewrite lookup_total_insert; unfold regval_into_reg; reflexivity).
    assert (Hm1 : m6 !!! Regidx a1_idx = cval).
    { unfold m6, m5, m4, m3, m2, m1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      unfold cval; reflexivity. }
    assert (Hsuf_sp : (<[Regidx a5_idx := regval_into_reg (ms_addr p (S N'))]> m6) !!! Regidx csp_rs1 = sp').
    { unfold m6, m5, m4, m3, m2, m1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite lookup_total_insert; unfold regval_into_reg; reflexivity. }
    assert (Hsuf_ra : (<[Regidx a5_idx := regval_into_reg (ms_addr p (S N'))]> m6) !!! Regidx ra_idx = ra0).
    { unfold m6, m5, m4, m3, m2, m1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      unfold ra0; reflexivity. }
    assert (Hpc1 : add_vec_int pcE 20 = pc0L) by (vm_compute; reflexivity).
    assert (Hpc2 : add_vec_int (add_vec_int pc0L 6) 4 = pcLS) by (vm_compute; reflexivity).
    (* --- PREFIX: 0xccc..0xcdc --- *)
    iApply (wp_memset_prefix_r R Φ m0 imm_entry shamt_l shamt_r nzimm_s0 imm8_beqz
              wval_add vra vs0 γ (dq:=dq)
 Hn0 Hvalue_add
              with "Hsm Htlbinv Hpc Hfile
                    Hi0 Hi2 Hi4 Hi6 Hi8 Hi10 Hi12 Hi14 Hi16 Hbra Hbs0 [-]").
    iIntros "Hsm Htlbinv Hpc Hfile Hbra Hbs0".
    iEval (rewrite Hpc1) in "Hpc".
    (* --- LOOP: 0xce0..0xce6 --- *)
    iApply (wp_memset_loop_r R γ Φ (S N') p e cval a1_idx a4_idx a5_idx imm_bne
              olds (dq:=dq)
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(intros j; exact (ms_incr_step p j)) Hcmp
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Hext0 Hext4 Hext6
              (S N') 0%nat m6 ltac:(reflexivity) ltac:(lia) Hcur Hm4 Hm1
              with "Hsm Htlbinv Htext Hpc Hfile Hbuf [-]").
    iIntros "Hsm Htlbinv Hpc Hfile Hbuf".
    iEval (rewrite Hpc2) in "Hpc".
    (* --- SUFFIX: 0xcea..ret --- *)
    iApply (wp_memset_suffix_r R Φ sp' ra0 s00 ra_idx s0_idx imm_dealloc
              (<[Regidx a5_idx := regval_into_reg (ms_addr p (S N'))]> m6)
              γ (dq:=dq)(dqm:=DfracOwn 1)
 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Hsuf_sp Hsuf_ra
              Hret0
              with "Hsm Htlbinv Hpc Hfile
                    HiL0 HiL2 HiL4 HiL6 Hbra Hbs0 [-]").
    iIntros "Hsm Htlbinv Hpc Hbra Hbs0 Hmfin".
    iDestruct "Hmfin" as (mfin) "[Hfile %Hpins]".
    destruct Hpins as (Hpra & Hps0 & Hpcsp & Hpres).
    (* rebundle the restored 2-slot frame back to [stack_own sp0 n] *)
    iEval (rewrite Hb1) in "Hbra". iEval (rewrite Hb2) in "Hbs0".
    iDestruct (stack_own_2_intro with "Hbra Hbs0") as "Htop".
    iDestruct (stack_own_split_2 sp0 2 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
    iApply ("Hcont" $! mfin with "Hsm Htlbinv Hpc Hstk Hbuf Hfile [%]").
    (* the caller-saved-register catch-all, relative to m0 *)
    assert (Hcatch : forall r : regidx,
              r <> Regidx ra_idx -> r <> Regidx s0_idx -> r <> Regidx csp_rs1 ->
              r <> Regidx a5_idx -> r <> Regidx a2_idx -> r <> Regidx a4_idx ->
              mfin !!! r = m0 !!! r).
    { intros r Hra Hs0 Hcsp Ha5 Ha2 Ha4.
      rewrite (Hpres r Hra Hs0 Hcsp).
      rewrite lookup_total_insert_ne; [| exact (not_eq_sym Ha5)].
      unfold m6, m5, m4, m3, m2, m1.
      rewrite lookup_total_insert_ne; [| exact (not_eq_sym Ha4)].
      rewrite lookup_total_insert_ne; [| exact (not_eq_sym Ha2)].
      rewrite lookup_total_insert_ne; [| exact (not_eq_sym Ha2)].
      rewrite lookup_total_insert_ne; [| exact (not_eq_sym Ha5)].
      rewrite lookup_total_insert_ne; [| exact (not_eq_sym Hs0)].
      rewrite lookup_total_insert_ne; [| exact (not_eq_sym Hcsp)].
      reflexivity. }
    unfold callee_saved. repeat split.
    - (* x2 sp: balanced frame *) rewrite Hpcsp. unfold sp'. apply Hframe.
    - (* x4 tp *) apply Hcatch; vm_compute; discriminate.
    - (* x8 s0 *) exact Hps0.
    - (* x9 s1 *) apply Hcatch; vm_compute; discriminate.
    - (* x18 s2 *) apply Hcatch; vm_compute; discriminate.
    - (* x19 s3 *) apply Hcatch; vm_compute; discriminate.
    - (* x20 s4 *) apply Hcatch; vm_compute; discriminate.
    - (* x21 s5 *) apply Hcatch; vm_compute; discriminate.
    - (* x22 s6 *) apply Hcatch; vm_compute; discriminate.
    - (* x23 s7 *) apply Hcatch; vm_compute; discriminate.
    - (* x24 s8 *) apply Hcatch; vm_compute; discriminate.
    - (* x25 s9 *) apply Hcatch; vm_compute; discriminate.
    - (* x26 s10 *) apply Hcatch; vm_compute; discriminate.
    - (* x27 s11 *) apply Hcatch; vm_compute; discriminate.
  Qed.

  Lemma wp_memset_s_full_kt (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m0 : gmap regidx (mword 64)) (N : nat) (wval_add : mword 64)
      (olds : nat -> bv 8) (n : nat)
      (γ : gname) {dq : dfrac} :
    let ra_idx : mword 5 := mword_of_int 1 in
    let s0_idx : mword 5 := mword_of_int 8 in
    let a0_idx : mword 5 := mword_of_int 10 in
    let a1_idx : mword 5 := mword_of_int 11 in
    let a2_idx : mword 5 := mword_of_int 12 in
    let a5_idx : mword 5 := mword_of_int 15 in
    let pcE := mword_of_int KernelSyms.memset in
    let imm_entry : mword 6 := mword_of_int 48 in
    let shamt_l : mword 6 := mword_of_int 32 in
    let shamt_r : mword 6 := mword_of_int 32 in
    let nzimm_s0 : mword 8 := mword_of_int 4 in
    let sp0 := m0 !!! Regidx csp_rs1 in
    let sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)) in
    let ra0 := m0 !!! Regidx ra_idx in
    let p := m0 !!! Regidx a0_idx in
    let e := wval_add in
    let cval := m0 !!! Regidx a1_idx in
    let m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0 in
    let m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1 in
    let m3 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2 in
    let m4 := <[Regidx a2_idx := regval_into_reg (shift_bits_left (m3 !!! Regidx a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3 in
    let m5 := <[Regidx a2_idx := regval_into_reg (shift_bits_right (m4 !!! Regidx a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4 in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    let cbyte := nth_byte (autocast (T := mword) (subrange_vec_dec cval (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 in
    (2 <= n)%nat ->
    (* the ADD computing the loop end pointer [a4 := a2 + a0 = wval_add] *)
    add_vec (m5 !!! Regidx a2_idx) (m5 !!! Regidx a0_idx) = wval_add ->
    (* the entry [beqz a2] is taken exactly when the byte count [N] is zero:
       count register is zero iff N = 0 (a 0-byte memset skips the loop) *)
    eq_vec (m0 !!! Regidx a2_idx) zero_reg = Nat.eqb N 0 ->
    (* caller's return target's low bit is clear (2-aligned Zca return) *)
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    (* the end pointer couples to the buffer: [wval_add = ms_addr p N] *)
    (forall j : nat, (j < N)%nat -> neq_vec (ms_addr p (S j)) e = negb (Nat.eqb (S j) N)) ->
    smode_config γ dq -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m0 -∗
    stack_own sp0 n -∗
    ([∗ list] j ∈ seq 0 N, (ms_pa (ms_addr p j)) ↦ₘ olds j) -∗
    ( ∀ mfin,
      smode_config γ dq -∗
      tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      stack_own sp0 n -∗
      ([∗ list] j ∈ seq 0 N, (ms_pa (ms_addr p j)) ↦ₘ cbyte) -∗
      gpr_file mfin -∗
      ⌜ callee_saved m0 mfin ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
    Proof.
    exact (wp_memset_s_full_kt_r (kpt_regime root_ppn) Φ m0 N wval_add olds n γ (dq:=dq)).
  Qed.

End WpMemsetInstr.
