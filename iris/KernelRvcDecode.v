(* KernelRvcDecode.v -- pure compressed-instruction decode facts for the
   instruction WORDS that appear in the kernel's shared spinlock function
   prologue / epilogue (frame setup, saved-register spill/reload, c.ret) plus
   the two creg->reg conversions they rely on.

   These are address-independent [exec (ext_decode_compressed w) s = Some (i, s)]
   equations under Misa.C=1 -- NOT weakest-preconditions -- so they live in this
   lightweight decode base rather than in any one function's WP file.  push_off,
   pop_off, holding, acquire, release and swtch all step the same compressed
   prologue/epilogue words and import this file for the decodes; none of them
   needs to depend on another's WP proof (or on mycpu) just to reach them. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvExec RiscvTryStep.
Require Import WpRvcBridge.
Require Import WpMmodeLeafBase.
Local Open Scope Z_scope.
Import Defs.

(* ---- creg -> reg conversions used by the shared prologue decodes ---- *)
Lemma po_cr2 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx (mword_of_int 10).
Proof. vm_compute. reflexivity. Qed.

Lemma po_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx (mword_of_int 15).
Proof. vm_compute. reflexivity. Qed.

(* ---- shared prologue / epilogue RVC decodes ---- *)

(* +0x00  0x1101  c.addi sp,-32 *)
Lemma podec_00 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1101 : mword 16)) s
  = Some (C_ADDI (mword_of_int 32, Regidx csp_rs1), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x02  0xec06  c.sdsp ra,24(sp) *)
Lemma podec_02 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xec06 : mword 16)) s
  = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 1)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x04  0xe822  c.sdsp s0,16(sp) *)
Lemma podec_04 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe822 : mword 16)) s
  = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 8)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x06  0xe426  c.sdsp s1,8(sp) *)
Lemma podec_06 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe426 : mword 16)) s
  = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 9)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x08  0x1000  c.addi4spn s0,sp,32 *)
Lemma podec_08 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1000 : mword 16)) s
  = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 8), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x0e  0x84be  c.mv s1,a5 *)
Lemma podec_0e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x84be : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 15)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x22  0x60e2  c.ldsp ra,24(sp) *)
Lemma podec_22 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x60e2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 1)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x24  0x6442  c.ldsp s0,16(sp) *)
Lemma podec_24 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6442 : mword 16)) s
  = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 8)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x26  0x64a2  c.ldsp s1,8(sp) *)
Lemma podec_26 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x64a2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 9)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x28  0x6105  c.addi16sp sp,32 *)
Lemma podec_28 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6105 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 2 : mword 6), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x2a  0x8082  c.ret *)
Lemma podec_2a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8082 : mword 16)) s
  = Some (C_JR (Regidx (mword_of_int 1)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* ---- shared push_off/pop_off instruction facts (both functions load/store the
   same mycpu-relative stack slot via the same c.lw a5,120(a0) / c.sw a5,120(a0);
   these live here beside po_cr2/po_cr7 so WpPushOffTop and WpPopOff share them
   rather than one depending on the other). ---- *)

(* +0x14/+0x1c  0x5d3c  c.lw a5,120(a0) *)
Lemma podec_lw s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x5d3c : mword 16)) s
  = Some (C_LW (mword_of_int 30, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x20  0xdd3c  c.sw a5,120(a0) *)
Lemma podec_sw120 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xdd3c : mword 16)) s
  = Some (C_SW (mword_of_int 30, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

Lemma po_imm120 : zero_extend' 12 (concat_vec (mword_of_int 30 : mword 5) ('b"00")) = (mword_of_int 120 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma poexec_lw s :
  exec (execute (C_LW (mword_of_int 30, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_LW. cbn zeta.
  rewrite exec_returnM. rewrite po_cr2. rewrite po_cr7. rewrite po_imm120. reflexivity.
Qed.

Lemma poexec_sw120 s :
  exec (execute (C_SW (mword_of_int 30, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 120, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_SW. cbn zeta.
  rewrite exec_returnM. rewrite po_cr2. rewrite po_cr7. rewrite po_imm120. reflexivity.
Qed.

Lemma po_addv_assoc (a b c : mword 64) :
  add_vec (add_vec a b) c = add_vec a (add_vec b c).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite !bv_add_unsigned.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, Z.add_assoc. reflexivity.
Qed.

(* ===================================================================== *)
(* Shared 16-byte stack-frame prologue/epilogue RVC decode templates       *)
(* (c.addi sp / c.sdsp / c.addi4spn / c.ldsp / c.ret), keyed by            *)
(* instruction bits.  Any function that uses the standard 16-byte frame     *)
(* (mycpu, memset, ...) reuses these from here, so no such proof imports    *)
(* another function's proof file just for its decode facts.                 *)
(* ===================================================================== *)
Lemma mdec_ccc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1141 : mword 16)) s = Some (C_ADDI (mword_of_int 48, Regidx csp_rs1), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma mdec_cce s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe406 : mword 16)) s = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma mdec_cd0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe022 : mword 16)) s = Some (C_SDSP (mword_of_int 0, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma mdec_cd2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0800 : mword 16)) s = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma mdec_cea s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x60a2 : mword 16)) s = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma mdec_cec s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6402 : mword 16)) s = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma mdec_cee s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0141 : mword 16)) s = Some (C_ADDI (mword_of_int 16, Regidx csp_rs1), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma mdec_cf0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8082 : mword 16)) s = Some (C_JR (Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.
