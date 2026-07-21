(* WpMycpu.v -- whole-function WP for xv6's mycpu() in S-mode.
   mycpu() @ 0x800018d6 returns a0 = &cpus[cpuid] (cpuid = tp register),
   using its own 16-byte stack frame (saves/restores ra,s0).  Built by
   composing the S-mode instruction lemmas (existing framework ones plus the
   new arithmetic/auipc lemmas in WpPushOff.v), following the stack-geometry
   composition pattern of WpKernelvecNew (wp_kernelvec) / WpMemsetS.

   Disassembly (KernelInstrs.v, symbol mycpu @ 0x800018d6):
     +0x00  800018d6  1141      c.addi   sp,sp,-16    frame alloc
     +0x02  800018d8  e406      c.sdsp   ra,8(sp)
     +0x04  800018da  e022      c.sdsp   s0,0(sp)
     +0x06  800018dc  0800      c.addi4spn s0,sp,16
     +0x08  800018de  8792      c.mv     a5,tp        a5 = cpuid
     +0x0a  800018e0  2781      c.addiw  a5,0         sext.w a5
     +0x0c  800018e2  079e      c.slli   a5,a5,0x7    a5 = cpuid<<7
     +0x0e  800018e4  00011517  auipc    a0,0x11
     +0x12  800018e8  a9450513  addi     a0,a0,-1388  a0 = &cpus
     +0x16  800018ec  953e      c.add    a0,a0,a5     a0 = &cpus[cpuid]
     +0x18  800018ee  60a2      c.ldsp   ra,8(sp)
     +0x1a  800018f0  6402      c.ldsp   s0,0(sp)
     +0x1c  800018f2  0141      c.addi   sp,sp,16     frame free
     +0x1e  800018f4  8082      c.ret                                        *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode WpLeafCommon KernelText WpAuipc.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.

(* mycpu's balanced frame: entry [addi sp,sp,-16] (imm 48 = -16 in 6-bit) and
   exit [addi sp,sp,+16] (imm 16) cancel, so sp returns to its entry value.
   (A local clone of WpMemsetPage.add_vec_frame_cancel, which lives downstream.) *)
Lemma mycpu_frame_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)) : mword 64)
             = 18446744073709551600) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
             = 16) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551600 + 16) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

(* [callee_saved] ignores ra (x1), so a preceding jal link-write on the input
   map is irrelevant: this lets a mycpu caller state its callee_saved post
   against the pre-jal map [m] while [wp_mycpu] proves it against the post-jal
   [<[ra:=..]> m]. *)

(* ===================================================================== *)
(* Decode templates.                                                      *)
(* ===================================================================== *)
Local Ltac my_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac my_close1 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; my_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

Local Ltac my_close2 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (Defs.and_boolM (returnM _)
                          (currentlyEnabled Ext_Zca))) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; my_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

(* ---- the six fresh decodes (bit patterns not shared with memset) ---- *)
(* +0x08  8792  c.mv a5,tp *)
Lemma mydec_mv s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8792 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 4)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x0a  2781  c.addiw a5,0 (sext.w) *)
Lemma mydec_addiw s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2781 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 0, Regidx (mword_of_int 15)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x0c  079e  c.slli a5,7 *)
Lemma mydec_slli s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x079e : mword 16)) s
  = Some (C_SLLI (mword_of_int 7, Regidx (mword_of_int 15)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x16  953e  c.add a0,a0,a5 *)
Lemma mydec_add s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x953e : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 10), Regidx (mword_of_int 15)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x0e  00011517  auipc a0,0x11 *)
Lemma mydec_auipc s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00011517 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x12  a9450513  addi a0,a0,-1388 *)
Lemma mydec_addi s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa8650513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xa86 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* ===================================================================== *)
(* The closed-form return value a0 = &cpus[cpuid].                        *)
(* ===================================================================== *)
Definition mycpu_a5 (tp0 : mword 64) : mword 64 :=
  shift_bits_left
    (sign_extend' 64 (subrange_vec_dec
       (add_vec (add_vec zero_reg tp0)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))
    (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0).

Definition mycpu_ret (tp0 : mword 64) : mword 64 :=
  add_vec
    (add_vec
       (add_vec (add_vec_int (mword_of_int KernelSyms.mycpu : mword 64) 14)
                (auipc_off (mword_of_int 0x11 : mword 20)))
       (sign_extend' 64 (mword_of_int 0xa86 : mword 12)))
    (mycpu_a5 tp0).


(* ---------------------------------------------------------------------- *)
(* The two straight-line blocks of mycpu, in the VCgen's alphabet.          *)
(* ---------------------------------------------------------------------- *)


(* variable convention: xk ↦ SX k 0 (from vregs_init); 33/34 = the two
   stack-slot contents at block entry. *)


(* the epilogue runs with sp already at sp' (the decremented value), so its
   stack slots sit at sp+8 / sp+0. *)


Section WpMycpu.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the fourteen mycpu instructions from [kernel_text]. *)
  (* ------------------------------------------------------------------- *)
  Lemma myi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.mycpu + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.

  Lemma myi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.mycpu + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.

  Lemma myi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.mycpu + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.

  Lemma myi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.mycpu + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.

  Lemma myi_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x08) : mword 64) true (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (KernelSyms.mycpu + 0x08)%Z (mword_of_int 0x8792 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x08) : mword 64) (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)) mydec_mv exec_execute_C_MV. Qed.

  Lemma myi_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x0a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (KernelSyms.mycpu + 0x0a)%Z (mword_of_int 0x2781 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x0a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) mydec_addiw exec_execute_C_ADDIW. Qed.

  Lemma myi_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x0c) : mword 64) true (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (KernelSyms.mycpu + 0x0c)%Z (mword_of_int 0x079e : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x0c) : mword 64) (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) mydec_slli exec_execute_C_SLLI. Qed.

  Lemma myi_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x0e) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KernelSyms.mycpu + 0x0e)%Z (mword_of_int 0x00011517 : mword 32)
    (mword_of_int (KernelSyms.mycpu + 0x0e) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)) mydec_auipc. Qed.

  Lemma myi_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x12) : mword 64) false (ITYPE (mword_of_int 0xa86 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KernelSyms.mycpu + 0x12)%Z (mword_of_int 0xa8650513 : mword 32)
    (mword_of_int (KernelSyms.mycpu + 0x12) : mword 64) (ITYPE (mword_of_int 0xa86 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) mydec_addi. Qed.

  Lemma myi_16 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x16) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.mycpu + 0x16)%Z (mword_of_int 0x953e : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)) mydec_add exec_execute_C_ADD. Qed.

  Lemma myi_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x18) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.mycpu + 0x18)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x18) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.

  Lemma myi_1a : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x1a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.mycpu + 0x1a)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x1a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.

  Lemma myi_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x1c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.mycpu + 0x1c)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x1c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.

  Lemma myi_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x1e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.mycpu + 0x1e)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x1e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the entire mycpu(), entry (0x800018d6) through *)
  (*  its return to the caller (PC = ra0 with the low bit cleared).         *)
  (*  Registers: ra=x1 sp=x2 tp=x4 s0=x8 a0=x10 a5=x15.                      *)
  (*  On exit a0 = &cpus[cpuid] = mycpu_ret (m0 !!! Regidx (mword_of_int 4)) *)
  (*  (the [a0] slot of the returned register file m11 equals mycpu_ret tp0),*)
  (*  a5 is clobbered, and ra/sp/s0 are restored (callee-saved).            *)
  (* =================================================================== *)
  (* the prologue's / epilogue's [instr] facts, from kernel_text via the
     existing WpMycpu decode templates. *)


  (* ------------------------------------------------------------------- *)


End WpMycpu.
