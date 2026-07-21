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
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode WpLeafCommon.
Require Import WpMmodeLeafBase.
Require Import SmodeCore KernelText WpMemsetS.
Require Import WpRvcBridge.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Local Open Scope Z_scope.
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



End WpMemsetInstr.
