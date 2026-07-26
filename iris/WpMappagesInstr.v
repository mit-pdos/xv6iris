(* WpMappagesInstr.v -- decode catalog for xv6's mappages() (kernel/vm.c).
   Per-instruction [instr] facts (mdec_* decode facts + mi_* instr lemmas),
   consumed by the wp_mappages proof; same architecture as WpWalkInstr.v.

   INSTRUCTION TABLE (kernel-rocq/KernelInstrs.v at KernelSyms.mappages =
   0x80001030; offsets relative; B = 4-byte base, C = RVC):

     +0x00 C 715d      addi  sp,sp,-80      (C_ADDI16SP)
     +0x02 C e486      sd    ra,72(sp)      (C_SDSP 9)
     +0x04 C e0a2      sd    s0,64(sp)      (C_SDSP 8)
     +0x06 C fc26      sd    s1,56(sp)      (C_SDSP 7)
     +0x08 C f84a      sd    s2,48(sp)      (C_SDSP 6)
     +0x0a C f44e      sd    s3,40(sp)      (C_SDSP 5)
     +0x0c C f052      sd    s4,32(sp)      (C_SDSP 4)
     +0x0e C ec56      sd    s5,24(sp)      (C_SDSP 3)
     +0x10 C e85a      sd    s6,16(sp)      (C_SDSP 2)
     +0x12 C e45e      sd    s7,8(sp)       (C_SDSP 1)
     +0x14 C 0880      addi  s0,sp,80       (C_ADDI4SPN)
     +0x16 B 03459793  slli  a5,a1,0x34     (va-alignment probe)
     +0x1a C eba1      bnez  a5,+0x50       (-> +0x6a panic; FALLS by the
                        va-aligned premise)
     +0x1c C 8a2a      mv    s4,a0          (s4 := pagetable)
     +0x1e C 8aba      mv    s5,a4          (s5 := perm)
     +0x20 B 03461793  slli  a5,a2,0x34     (size-alignment probe)
     +0x24 C eba9      bnez  a5,+0x52       (-> +0x76 panic; FALLS)
     +0x26 C ce31      beqz  a2,+0x5c       (-> +0x82 panic; FALLS by
                        npages >= 1)
     +0x28 B 80060613  addi  a2,a2,-2048
     +0x2c B 80060613  addi  a2,a2,-2048    (a2 := size - 4096)
     +0x30 B 00b60933  add   s2,a2,a1       (s2 := last va)
     +0x34 C 84ae      mv    s1,a1          (s1 := va, the loop var)
     +0x36 C 4b05      li    s6,1
     +0x38 B 40b689b3  sub   s3,a3,a1       (s3 := pa - va)
     +0x3c C 6b85      lui   s7,0x1         (s7 := 4096)
     +0x3e C 865a      mv    a2,s6          <- LOOP HEAD
     +0x40 C 85a6      mv    a1,s1
     +0x42 C 8552      mv    a0,s4
     +0x44 B ee9ff0ef  jal   walk           (SpecWalk.wp_walk_sconf)
     +0x48 C c929      beqz  a0,+0x52       (-> +0xca: ret -1 exit)
     +0x4a C 611c      ld    a5,0(a0)       (the REMAP-CHECK read)
     +0x4c C 8b85      andi  a5,a5,1
     +0x4e C e3a1      bnez  a5,+0x40       (-> +0xbe remap panic; FALLS:
                        the L0 word is ZERO by pt_rep0 + no-remap)
     +0x50 B 013487b3  add   a5,s1,s3       (a5 := pa of this page)
     +0x54 C 83b1      srli  a5,a5,0xc
     +0x56 C 07aa      slli  a5,a5,0xa
     +0x58 B 0157e7b3  or    a5,a5,s5
     +0x5c B 0017e793  ori   a5,a5,1        (a5 := PA2PTE|perm|V)
     +0x60 C e11c      sd    a5,0(a0)       (the LEAF WRITE)
     +0x62 B 05248863  beq   s1,s2,+0x50    (-> +0xb2: ret 0 exit)
     +0x66 C 94de      add   s1,s1,s7       (va += PGSIZE)
     +0x68 C bfd9      j     -0x2a          (-> +0x3e loop)
     +0x6a..+0x98      five panic arms      (UNREACHABLE; no facts)
     +0x9a C 557d      li    a0,-1
     +0x9c C 60a6      ld    ra,72(sp)      (C_LDSP 9)   <- EPILOGUE
     +0x9e C 6406      ld    s0,64(sp)      (C_LDSP 8)
     +0xa0 C 74e2      ld    s1,56(sp)      (C_LDSP 7)
     +0xa2 C 7942      ld    s2,48(sp)      (C_LDSP 6)
     +0xa4 C 79a2      ld    s3,40(sp)      (C_LDSP 5)
     +0xa6 C 7a02      ld    s4,32(sp)      (C_LDSP 4)
     +0xa8 C 6ae2      ld    s5,24(sp)      (C_LDSP 3)
     +0xaa C 6b42      ld    s6,16(sp)      (C_LDSP 2)
     +0xac C 6ba2      ld    s7,8(sp)       (C_LDSP 1)
     +0xae C 6161      addi  sp,sp,80       (C_ADDI16SP)
     +0xb0 C 8082      ret                  (C_JR ra)
     +0xb2 C 4501      li    a0,0
     +0xb4 C b7e5      j     -0x18          (-> +0xcc epilogue)          *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes KernelText.
Require Import WpDecode WpDecodeBridge WpRvcBridge.
Require Import WpMmodeLeafBase.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Import Defs.

Section MappagesInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Local Notation MPP off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.mappages + off) : mword 64) rvc ast).
  Local Notation csdsp_imm u :=
    (zero_extend' 12 (concat_vec (mword_of_int u : mword 6) ('b"000"))) (only parsing).

  (* ExecuteAs redirects not in WpMmodeLeafBase (Local copies, as in
     WpWalkInstr) *)
  Lemma mdec_16 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x03459793 : mword 32)) s
    = Some (SHIFTIOP (mword_of_int 52 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 15), SLLI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma mdec_1a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xeba1 : mword 16)) s
    = Some (C_BNEZ (mword_of_int 40, Cregidx (mword_of_int 7)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_1e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x8aba : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 21), Regidx (mword_of_int 14)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_20 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x03461793 : mword 32)) s
    = Some (SHIFTIOP (mword_of_int 52 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 15), SLLI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma mdec_24 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xeba9 : mword 16)) s
    = Some (C_BNEZ (mword_of_int 41, Cregidx (mword_of_int 7)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_26 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xce31 : mword 16)) s
    = Some (C_BEQZ (mword_of_int 46, Cregidx (mword_of_int 4)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_28 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x80060613 : mword 32)) s
    = Some (ITYPE (mword_of_int 2048 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma mdec_30 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00b60933 : mword 32)) s
    = Some (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 12), Regidx (mword_of_int 18), ADD), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma mdec_34 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x84ae : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 11)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_36 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x4b05 : mword 16)) s
    = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 22)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_38 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x40b689b3 : mword 32)) s
    = Some (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 13), Regidx (mword_of_int 19), SUB), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma mdec_3c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6b85 : mword 16)) s
    = Some (C_LUI (mword_of_int 1, Regidx (mword_of_int 23)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_3e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x865a : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 22)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_40 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x85a6 : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 9)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_44 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xee9ff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2096872 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma mdec_48 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xc929 : mword 16)) s
    = Some (C_BEQZ (mword_of_int 41, Cregidx (mword_of_int 2)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_4a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x611c : mword 16)) s
    = Some (C_LD (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_4e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe3a1 : mword 16)) s
    = Some (C_BNEZ (mword_of_int 32, Cregidx (mword_of_int 7)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_50 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x013487b3 : mword 32)) s
    = Some (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 9), Regidx (mword_of_int 15), ADD), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma mdec_58 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x0157e7b3 : mword 32)) s
    = Some (RTYPE (Regidx (mword_of_int 21), Regidx (mword_of_int 15), Regidx (mword_of_int 15), OR), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma mdec_5c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x0017e793 : mword 32)) s
    = Some (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ORI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma mdec_60 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe11c : mword 16)) s
    = Some (C_SD (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_62 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x05248863 : mword 32)) s
    = Some (BTYPE (mword_of_int 80 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BEQ), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma mdec_66 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x94de : mword 16)) s
    = Some (C_ADD (Regidx (mword_of_int 9), Regidx (mword_of_int 23)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma mdec_9a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x557d : mword 16)) s
    = Some (C_LI (mword_of_int 63, Regidx (mword_of_int 10)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  (* ---- instr lemmas ---- *)
  Lemma mi_00 : MPP 0x00 true (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.mappages + 0x00)%Z (mword_of_int 0x715d : mword 16) (mword_of_int (KernelSyms.mappages + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)) cdec_715d exec_execute_C_ADDI16SP. Qed.
  Lemma mi_02 : MPP 0x02 true (STORE (csdsp_imm 9, Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0x02)%Z (mword_of_int 0xe486 : mword 16) (mword_of_int (KernelSyms.mappages + 0x02) : mword 64) (STORE (csdsp_imm 9, Regidx (mword_of_int 1), sp, 8)) cdec_e486 exec_execute_C_SDSP. Qed.
  Lemma mi_04 : MPP 0x04 true (STORE (csdsp_imm 8, Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0x04)%Z (mword_of_int 0xe0a2 : mword 16) (mword_of_int (KernelSyms.mappages + 0x04) : mword 64) (STORE (csdsp_imm 8, Regidx (mword_of_int 8), sp, 8)) cdec_e0a2 exec_execute_C_SDSP. Qed.
  Lemma mi_06 : MPP 0x06 true (STORE (csdsp_imm 7, Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0x06)%Z (mword_of_int 0xfc26 : mword 16) (mword_of_int (KernelSyms.mappages + 0x06) : mword 64) (STORE (csdsp_imm 7, Regidx (mword_of_int 9), sp, 8)) cdec_fc26 exec_execute_C_SDSP. Qed.
  Lemma mi_08 : MPP 0x08 true (STORE (csdsp_imm 6, Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0x08)%Z (mword_of_int 0xf84a : mword 16) (mword_of_int (KernelSyms.mappages + 0x08) : mword 64) (STORE (csdsp_imm 6, Regidx (mword_of_int 18), sp, 8)) cdec_f84a exec_execute_C_SDSP. Qed.
  Lemma mi_0a : MPP 0x0a true (STORE (csdsp_imm 5, Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0x0a)%Z (mword_of_int 0xf44e : mword 16) (mword_of_int (KernelSyms.mappages + 0x0a) : mword 64) (STORE (csdsp_imm 5, Regidx (mword_of_int 19), sp, 8)) cdec_f44e exec_execute_C_SDSP. Qed.
  Lemma mi_0c : MPP 0x0c true (STORE (csdsp_imm 4, Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0x0c)%Z (mword_of_int 0xf052 : mword 16) (mword_of_int (KernelSyms.mappages + 0x0c) : mword 64) (STORE (csdsp_imm 4, Regidx (mword_of_int 20), sp, 8)) cdec_f052 exec_execute_C_SDSP. Qed.
  Lemma mi_0e : MPP 0x0e true (STORE (csdsp_imm 3, Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0x0e)%Z (mword_of_int 0xec56 : mword 16) (mword_of_int (KernelSyms.mappages + 0x0e) : mword 64) (STORE (csdsp_imm 3, Regidx (mword_of_int 21), sp, 8)) cdec_ec56 exec_execute_C_SDSP. Qed.
  Lemma mi_10 : MPP 0x10 true (STORE (csdsp_imm 2, Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0x10)%Z (mword_of_int 0xe85a : mword 16) (mword_of_int (KernelSyms.mappages + 0x10) : mword 64) (STORE (csdsp_imm 2, Regidx (mword_of_int 22), sp, 8)) cdec_e85a exec_execute_C_SDSP. Qed.
  Lemma mi_12 : MPP 0x12 true (STORE (csdsp_imm 1, Regidx (mword_of_int 23), sp, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0x12)%Z (mword_of_int 0xe45e : mword 16) (mword_of_int (KernelSyms.mappages + 0x12) : mword 64) (STORE (csdsp_imm 1, Regidx (mword_of_int 23), sp, 8)) cdec_e45e exec_execute_C_SDSP. Qed.
  Lemma mi_14 : MPP 0x14 true (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.mappages + 0x14)%Z (mword_of_int 0x0880 : mword 16) (mword_of_int (KernelSyms.mappages + 0x14) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0880 exec_execute_C_ADDI4SPN. Qed.
  Lemma mi_16 : MPP 0x16 false (SHIFTIOP (mword_of_int 52 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_base (KernelSyms.mappages + 0x16)%Z (mword_of_int 0x03459793 : mword 32) (mword_of_int (KernelSyms.mappages + 0x16) : mword 64) (SHIFTIOP (mword_of_int 52 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 15), SLLI)) mdec_16. Qed.
  Lemma mi_1a : MPP 0x1a true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 40 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (KernelSyms.mappages + 0x1a)%Z (mword_of_int 0xeba1 : mword 16) (mword_of_int (KernelSyms.mappages + 0x1a) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 40 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) mdec_1a exec_execute_C_BNEZ. Qed.
  Lemma mi_1c : MPP 0x1c true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (KernelSyms.mappages + 0x1c)%Z (mword_of_int 0x8a2a : mword 16) (mword_of_int (KernelSyms.mappages + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)) cdec_8a2a exec_execute_C_MV. Qed.
  Lemma mi_1e : MPP 0x1e true (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 21), ADD)).
  Proof. mk_rvc (KernelSyms.mappages + 0x1e)%Z (mword_of_int 0x8aba : mword 16) (mword_of_int (KernelSyms.mappages + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 21), ADD)) mdec_1e exec_execute_C_MV. Qed.
  Lemma mi_20 : MPP 0x20 false (SHIFTIOP (mword_of_int 52 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_base (KernelSyms.mappages + 0x20)%Z (mword_of_int 0x03461793 : mword 32) (mword_of_int (KernelSyms.mappages + 0x20) : mword 64) (SHIFTIOP (mword_of_int 52 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 15), SLLI)) mdec_20. Qed.
  Lemma mi_24 : MPP 0x24 true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 41 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (KernelSyms.mappages + 0x24)%Z (mword_of_int 0xeba9 : mword 16) (mword_of_int (KernelSyms.mappages + 0x24) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 41 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) mdec_24 exec_execute_C_BNEZ. Qed.
  Lemma mi_26 : MPP 0x26 true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 46 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)).
  Proof. mk_rvc (KernelSyms.mappages + 0x26)%Z (mword_of_int 0xce31 : mword 16) (mword_of_int (KernelSyms.mappages + 0x26) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 46 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)) mdec_26 exec_execute_C_BEQZ. Qed.
  Lemma mi_28 : MPP 0x28 false (ITYPE (mword_of_int 2048 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (KernelSyms.mappages + 0x28)%Z (mword_of_int 0x80060613 : mword 32) (mword_of_int (KernelSyms.mappages + 0x28) : mword 64) (ITYPE (mword_of_int 2048 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)) mdec_28. Qed.
  Lemma mi_2c : MPP 0x2c false (ITYPE (mword_of_int 2048 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (KernelSyms.mappages + 0x2c)%Z (mword_of_int 0x80060613 : mword 32) (mword_of_int (KernelSyms.mappages + 0x2c) : mword 64) (ITYPE (mword_of_int 2048 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)) mdec_28. Qed.
  Lemma mi_30 : MPP 0x30 false (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 12), Regidx (mword_of_int 18), ADD)).
  Proof. mk_base (KernelSyms.mappages + 0x30)%Z (mword_of_int 0x00b60933 : mword 32) (mword_of_int (KernelSyms.mappages + 0x30) : mword 64) (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 12), Regidx (mword_of_int 18), ADD)) mdec_30. Qed.
  Lemma mi_34 : MPP 0x34 true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.mappages + 0x34)%Z (mword_of_int 0x84ae : mword 16) (mword_of_int (KernelSyms.mappages + 0x34) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)) mdec_34 exec_execute_C_MV. Qed.
  Lemma mi_36 : MPP 0x36 true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 22), ADDI)).
  Proof. mk_rvc (KernelSyms.mappages + 0x36)%Z (mword_of_int 0x4b05 : mword 16) (mword_of_int (KernelSyms.mappages + 0x36) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 22), ADDI)) mdec_36 exec_execute_C_LI. Qed.
  Lemma mi_38 : MPP 0x38 false (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 13), Regidx (mword_of_int 19), SUB)).
  Proof. mk_base (KernelSyms.mappages + 0x38)%Z (mword_of_int 0x40b689b3 : mword 32) (mword_of_int (KernelSyms.mappages + 0x38) : mword 64) (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 13), Regidx (mword_of_int 19), SUB)) mdec_38. Qed.
  Lemma mi_3c : MPP 0x3c true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 23), LUI)).
  Proof. mk_rvc (KernelSyms.mappages + 0x3c)%Z (mword_of_int 0x6b85 : mword 16) (mword_of_int (KernelSyms.mappages + 0x3c) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 23), LUI)) mdec_3c exec_execute_C_LUI. Qed.
  Lemma mi_3e : MPP 0x3e true (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (KernelSyms.mappages + 0x3e)%Z (mword_of_int 0x865a : mword 16) (mword_of_int (KernelSyms.mappages + 0x3e) : mword 64) (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 12), ADD)) mdec_3e exec_execute_C_MV. Qed.
  Lemma mi_40 : MPP 0x40 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (KernelSyms.mappages + 0x40)%Z (mword_of_int 0x85a6 : mword 16) (mword_of_int (KernelSyms.mappages + 0x40) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)) mdec_40 exec_execute_C_MV. Qed.
  Lemma mi_42 : MPP 0x42 true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.mappages + 0x42)%Z (mword_of_int 0x8552 : mword 16) (mword_of_int (KernelSyms.mappages + 0x42) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)) cdec_8552 exec_execute_C_MV. Qed.
  Lemma mi_44 : MPP 0x44 false (JAL (mword_of_int 2096872 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.mappages + 0x44)%Z (mword_of_int 0xee9ff0ef : mword 32) (mword_of_int (KernelSyms.mappages + 0x44) : mword 64) (JAL (mword_of_int 2096872 : mword 21, Regidx (mword_of_int 1))) mdec_44. Qed.
  Lemma mi_48 : MPP 0x48 true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 41 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (KernelSyms.mappages + 0x48)%Z (mword_of_int 0xc929 : mword 16) (mword_of_int (KernelSyms.mappages + 0x48) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 41 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) mdec_48 exec_execute_C_BEQZ. Qed.
  Lemma mi_4a : MPP 0x4a true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0x4a)%Z (mword_of_int 0x611c : mword 16) (mword_of_int (KernelSyms.mappages + 0x4a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) mdec_4a exec_execute_C_LD. Qed.
  Lemma mi_4c : MPP 0x4c true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), ANDI)).
  Proof. mk_rvc (KernelSyms.mappages + 0x4c)%Z (mword_of_int 0x8b85 : mword 16) (mword_of_int (KernelSyms.mappages + 0x4c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), ANDI)) cdec_8b85 exec_execute_C_ANDI. Qed.
  Lemma mi_4e : MPP 0x4e true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 32 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (KernelSyms.mappages + 0x4e)%Z (mword_of_int 0xe3a1 : mword 16) (mword_of_int (KernelSyms.mappages + 0x4e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 32 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) mdec_4e exec_execute_C_BNEZ. Qed.
  Lemma mi_50 : MPP 0x50 false (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 9), Regidx (mword_of_int 15), ADD)).
  Proof. mk_base (KernelSyms.mappages + 0x50)%Z (mword_of_int 0x013487b3 : mword 32) (mword_of_int (KernelSyms.mappages + 0x50) : mword 64) (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 9), Regidx (mword_of_int 15), ADD)) mdec_50. Qed.
  Lemma mi_54 : MPP 0x54 true (SHIFTIOP (mword_of_int 12 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)).
  Proof. mk_rvc (KernelSyms.mappages + 0x54)%Z (mword_of_int 0x83b1 : mword 16) (mword_of_int (KernelSyms.mappages + 0x54) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)) cdec_83b1 exec_execute_C_SRLI. Qed.
  Lemma mi_56 : MPP 0x56 true (SHIFTIOP (mword_of_int 10 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (KernelSyms.mappages + 0x56)%Z (mword_of_int 0x07aa : mword 16) (mword_of_int (KernelSyms.mappages + 0x56) : mword 64) (SHIFTIOP (mword_of_int 10 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) cdec_07aa exec_execute_C_SLLI. Qed.
  Lemma mi_58 : MPP 0x58 false (RTYPE (Regidx (mword_of_int 21), Regidx (mword_of_int 15), Regidx (mword_of_int 15), OR)).
  Proof. mk_base (KernelSyms.mappages + 0x58)%Z (mword_of_int 0x0157e7b3 : mword 32) (mword_of_int (KernelSyms.mappages + 0x58) : mword 64) (RTYPE (Regidx (mword_of_int 21), Regidx (mword_of_int 15), Regidx (mword_of_int 15), OR)) mdec_58. Qed.
  Lemma mi_5c : MPP 0x5c false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ORI)).
  Proof. mk_base (KernelSyms.mappages + 0x5c)%Z (mword_of_int 0x0017e793 : mword 32) (mword_of_int (KernelSyms.mappages + 0x5c) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ORI)) mdec_5c. Qed.
  Lemma mi_60 : MPP 0x60 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0x60)%Z (mword_of_int 0xe11c : mword 16) (mword_of_int (KernelSyms.mappages + 0x60) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), 8)) mdec_60 exec_execute_C_SD. Qed.
  Lemma mi_62 : MPP 0x62 false (BTYPE (mword_of_int 80 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BEQ)).
  Proof. mk_base (KernelSyms.mappages + 0x62)%Z (mword_of_int 0x05248863 : mword 32) (mword_of_int (KernelSyms.mappages + 0x62) : mword 64) (BTYPE (mword_of_int 80 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BEQ)) mdec_62. Qed.
  Lemma mi_66 : MPP 0x66 true (RTYPE (Regidx (mword_of_int 23), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.mappages + 0x66)%Z (mword_of_int 0x94de : mword 16) (mword_of_int (KernelSyms.mappages + 0x66) : mword 64) (RTYPE (Regidx (mword_of_int 23), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADD)) mdec_66 exec_execute_C_ADD. Qed.
  Lemma mi_68 : MPP 0x68 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.mappages + 0x68)%Z (mword_of_int 0xbfd9 : mword 16) (mword_of_int (KernelSyms.mappages + 0x68) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")), zreg)) cdec_bfd9 exec_execute_C_J. Qed.
  Lemma mi_9a : MPP 0x9a true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KernelSyms.mappages + 0x9a)%Z (mword_of_int 0x557d : mword 16) (mword_of_int (KernelSyms.mappages + 0x9a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) mdec_9a exec_execute_C_LI. Qed.
  Lemma mi_9c : MPP 0x9c true (LOAD (csdsp_imm 9, sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0x9c)%Z (mword_of_int 0x60a6 : mword 16) (mword_of_int (KernelSyms.mappages + 0x9c) : mword 64) (LOAD (csdsp_imm 9, sp, Regidx (mword_of_int 1), false, 8)) cdec_60a6 exec_execute_C_LDSP. Qed.
  Lemma mi_9e : MPP 0x9e true (LOAD (csdsp_imm 8, sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0x9e)%Z (mword_of_int 0x6406 : mword 16) (mword_of_int (KernelSyms.mappages + 0x9e) : mword 64) (LOAD (csdsp_imm 8, sp, Regidx (mword_of_int 8), false, 8)) cdec_6406 exec_execute_C_LDSP. Qed.
  Lemma mi_a0 : MPP 0xa0 true (LOAD (csdsp_imm 7, sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0xa0)%Z (mword_of_int 0x74e2 : mword 16) (mword_of_int (KernelSyms.mappages + 0xa0) : mword 64) (LOAD (csdsp_imm 7, sp, Regidx (mword_of_int 9), false, 8)) cdec_74e2 exec_execute_C_LDSP. Qed.
  Lemma mi_a2 : MPP 0xa2 true (LOAD (csdsp_imm 6, sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0xa2)%Z (mword_of_int 0x7942 : mword 16) (mword_of_int (KernelSyms.mappages + 0xa2) : mword 64) (LOAD (csdsp_imm 6, sp, Regidx (mword_of_int 18), false, 8)) cdec_7942 exec_execute_C_LDSP. Qed.
  Lemma mi_a4 : MPP 0xa4 true (LOAD (csdsp_imm 5, sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0xa4)%Z (mword_of_int 0x79a2 : mword 16) (mword_of_int (KernelSyms.mappages + 0xa4) : mword 64) (LOAD (csdsp_imm 5, sp, Regidx (mword_of_int 19), false, 8)) cdec_79a2 exec_execute_C_LDSP. Qed.
  Lemma mi_a6 : MPP 0xa6 true (LOAD (csdsp_imm 4, sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0xa6)%Z (mword_of_int 0x7a02 : mword 16) (mword_of_int (KernelSyms.mappages + 0xa6) : mword 64) (LOAD (csdsp_imm 4, sp, Regidx (mword_of_int 20), false, 8)) cdec_7a02 exec_execute_C_LDSP. Qed.
  Lemma mi_a8 : MPP 0xa8 true (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0xa8)%Z (mword_of_int 0x6ae2 : mword 16) (mword_of_int (KernelSyms.mappages + 0xa8) : mword 64) (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 21), false, 8)) cdec_6ae2 exec_execute_C_LDSP. Qed.
  Lemma mi_aa : MPP 0xaa true (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0xaa)%Z (mword_of_int 0x6b42 : mword 16) (mword_of_int (KernelSyms.mappages + 0xaa) : mword 64) (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 22), false, 8)) cdec_6b42 exec_execute_C_LDSP. Qed.
  Lemma mi_ac : MPP 0xac true (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 23), false, 8)).
  Proof. mk_rvc (KernelSyms.mappages + 0xac)%Z (mword_of_int 0x6ba2 : mword 16) (mword_of_int (KernelSyms.mappages + 0xac) : mword 64) (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 23), false, 8)) cdec_6ba2 exec_execute_C_LDSP. Qed.
  Lemma mi_ae : MPP 0xae true (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.mappages + 0xae)%Z (mword_of_int 0x6161 : mword 16) (mword_of_int (KernelSyms.mappages + 0xae) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)) cdec_6161 exec_execute_C_ADDI16SP. Qed.
  Lemma mi_b0 : MPP 0xb0 true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.mappages + 0xb0)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int (KernelSyms.mappages + 0xb0) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.
  Lemma mi_b2 : MPP 0xb2 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KernelSyms.mappages + 0xb2)%Z (mword_of_int 0x4501 : mword 16) (mword_of_int (KernelSyms.mappages + 0xb2) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.
  Lemma mi_b4 : MPP 0xb4 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.mappages + 0xb4)%Z (mword_of_int 0xb7e5 : mword 16) (mword_of_int (KernelSyms.mappages + 0xb4) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")), zreg)) cdec_b7e5 exec_execute_C_J. Qed.

End MappagesInstrs.
