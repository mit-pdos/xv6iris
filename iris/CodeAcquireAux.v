(* CodeAcquireAux.v -- decode/leaf lemmas for xv6's acquire() in S-mode: one
   [instr] lemma per instruction of acquire() (aqi_00 .. aqi_32) plus the
   underlying decode/execute facts they build on (aqdec_*, aqexec_sd, add_vec_zero_l, aq_sextw_round, ...).  These are consumed by
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
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode ExecCommon KernelText.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode KernelBaseDecode.
Require Import WpAmo.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Import CodeAcquire.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode lemmas for the encodings not already covered by CodePushOff /  *)
(* CodeMycpu / CodeHolding / WpAmo.                                           *)
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

(* +0x1a  0x87ba  c.mv a5,a4 *)

(* +0x18  0xed11  c.bnez a0,+0x1c *)

(* +0x22  0xffe5  c.bnez a5,-8 *)

(* ---- base (4-byte) decodes: the three jal's ---- *)
Local Ltac aq_dbase s Hpriv :=
  decode_pause_prefix s Hpriv;
  match goal with |- ?lhs = ?rhs =>
    let l := eval vm_compute in lhs in change_no_check (l = rhs) end;
  aq_ast.

(* +0x0c  0xfbbff0ef  jal ra,push_off (offset -0x46) *)

(* +0x12  0xf89ff0ef  jal ra,holding (offset -0x78) *)

(* ---- the panic arm (+0x34 .. +0x3c): auipc a0 / addi a0 / jal panic ---- *)
(* +0x34  0x00006517  auipc a0,0x6 *)
(* [bdec_00006517] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* +0x38  0x40c50513  addi a0,a0,1036 *)

(* +0x3c  0xbe3ff0ef  jal ra,panic (offset -0x41e) *)

(* +0x24  0x4b9000ef  jal ra,mycpu (offset +0xcb8) *)

(* ---- creg / ExecuteAs expansions ---- *)

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

Section CodeAcquireAux.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the panic arm: the c.bnez at +0x18 lands here when holding() said 1. *)

End CodeAcquireAux.
