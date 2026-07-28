(* WpWalkInstr.v -- decode catalog for xv6's walk() (kernel/vm.c), the
   3-level Sv39 page-table walk with allocation.  This file will hold the
   per-instruction [instr] facts (wdec_* RVC decode facts via rvc_oneshot
   + wi_* instr lemmas via mk_rvc/mk_base), consumed by the wp_walk proof.

   INSTRUCTION TABLE (from kernel-rocq/KernelInstrs.v at KernelSyms.walk =
   0x80000f5c; offsets relative; B = 4-byte base, C = RVC.  The wkd_*
   decode facts in WpWakeup.v cover many of the frame bytes -- copy their
   proven AST shapes; the ALU leaves for srl/andi/ori/c.slli/c.srli are
   wp_{srl,andi,ori,cslli,csrli}_s_r in WpSmodePtAlu.v):

     +0x00 C 7139      addi  sp,sp,-64      (C_ADDI16SP; wakeup cdec_7139)
     +0x02 C fc06      sd    ra,56(sp)      (C_SDSP 7)
     +0x04 C f822      sd    s0,48(sp)      (C_SDSP 6)
     +0x06 C f426      sd    s1,40(sp)      (C_SDSP 5)
     +0x08 C f04a      sd    s2,32(sp)      (C_SDSP 4)
     +0x0a C ec4e      sd    s3,24(sp)      (C_SDSP 3)
     +0x0c C e852      sd    s4,16(sp)      (C_SDSP 2)
     +0x0e C e456      sd    s5,8(sp)       (C_SDSP 1)
     +0x10 C e05a      sd    s6,0(sp)       (C_SDSP 0)
     +0x12 C 0080      addi  s0,sp,64       (C_ADDI4SPN)
     +0x14 C 84aa      mv    s1,a0          (C_MV)
     +0x16 C 89ae      mv    s3,a1          (C_MV)
     +0x18 C 8b32      mv    s6,a2          (C_MV)
     +0x1a C 57fd      li    a5,-1          (C_LI)
     +0x1c C 83e9      srli  a5,a5,0x1a     (C_SRLI; leaf wp_csrli_s_r)
     +0x1e C 4a79      li    s4,30          (C_LI)
     +0x20 C 4ab1      li    s5,12          (C_LI)
     +0x22 B 04b7e263  bltu  a5,a1,+0x44    (-> +0x66 panic arm; FALL
                        through under the va < 2^38 premise)
     +0x26 B 0149d933  srl   s2,s3,s4       (leaf wp_srl_s_r)   <- LOOP
     +0x2a B 1ff97913  andi  s2,s2,511      (leaf wp_andi_s_r)
     +0x2e C 090e      slli  s2,s2,0x3      (C_SLLI; wp_cslli_s_r)
     +0x30 C 9926      add   s2,s2,s1       (C_ADD)
     +0x32 B 00093483  ld    s1,0(s2)       (the SLOT READ: wp_ld_s_r
                        through ptree_own_slot2_ro / slot1_ro cells)
     +0x36 B 0014f793  andi  a5,s1,1        (wp_andi_s_r; the V-bit test)
     +0x3a C cf85      beqz  a5,+0x38       (-> +0x72 alloc arm)
     +0x3c C 80a9      srli  s1,s1,0xa      (C_SRLI)
     +0x3e C 04b2      slli  s1,s1,0xc      (C_SLLI; s1 := next base;
                        needs pte_valid_ptr_ext0 for the address bridge)
     +0x40 C 3a5d      addiw s4,s4,-9       (C_ADDIW)
     +0x42 B ff5a12e3  bne   s4,s5,-0x1c    (-> +0x26 loop back; TAKEN
                        once: 21 <> 12; falls through when s4 = 12)
     +0x46 B 00c9d513  srli  a0,s3,0xc      (base SRLI; wp_srli4_s_r)
     +0x4a B 1ff57513  andi  a0,a0,511      (wp_andi_s_r)
     +0x4e C 050e      slli  a0,a0,0x3      (C_SLLI)
     +0x50 C 9526      add   a0,a0,s1       (C_ADD; a0 := pt_addr0)
     +0x52 C 70e2      ld    ra,56(sp)      (C_LDSP 7)
     +0x54 C 7442      ld    s0,48(sp)      (C_LDSP 6)
     +0x56 C 74a2      ld    s1,40(sp)      (C_LDSP 5)
     +0x58 C 7902      ld    s2,32(sp)      (C_LDSP 4)
     +0x5a C 69e2      ld    s3,24(sp)      (C_LDSP 3)
     +0x5c C 6a42      ld    s4,16(sp)      (C_LDSP 2)
     +0x5e C 6aa2      ld    s5,8(sp)       (C_LDSP 1)
     +0x60 C 6b02      ld    s6,0(sp)       (C_LDSP 0)
     +0x62 C 6121      addi  sp,sp,64       (C_ADDI16SP)
     +0x64 C 8082      ret                  (C_JR ra; kdec_ret)
     +0x66 B 00006517  auipc a0,0x6         (panic arm -- UNREACHABLE
     +0x6a B 0ee50513  addi  a0,a0,238       under the va < 2^38 premise;
     +0x6e B 85dff0ef  jal   panic           no decode facts needed)
     +0x72 B 020b0263  beqz  s6,+0x24       (-> +0x96 alloc=0 arm; FALLS
                        through under the alloc=1 premise)
     +0x76 B b5dff0ef  jal   kalloc         (wp_kalloc at the regime)
     +0x7a C 84aa      mv    s1,a0          (C_MV)
     +0x7c C d979      beqz  a0,-0x2a       (-> +0x52 epilogue with a0=0:
                        the kalloc-null exit, spec's left disjunct)
     +0x7e C 6605      lui   a2,0x1         (C_LUI)
     +0x80 C 4581      li    a1,0           (C_LI)
     +0x82 B cebff0ef  jal   memset         (wp_memset_s_full_kt_r --
                        keeps the concrete zero bytes for
                        zero_page_to_node)
     +0x86 B 00c4d793  srli  a5,s1,0xc      (base SRLI)
     +0x8a C 07aa      slli  a5,a5,0xa      (C_SLLI)
     +0x8c B 0017e793  ori   a5,a5,1        (wp_ori_s_r; a5 := pt_ptr_pte)
     +0x90 B 00f93023  sd    a5,0(s2)       (the SLOT WRITE: wp_sd_s_r
                        through ptree_own_graft2/_graft1's cell)
     +0x94 C b775      j     -0x0c          (-> +0x40 rejoin loop
                        decrement; C_J back edge)
     +0x96 C 4501      li    a0,0           (C_LI; alloc=0 arm --
                        UNREACHABLE under the alloc=1 premise, but the
     +0x98 C bf6d      j     -0x46           LIVE path of walk called with
                        alloc = 0; -> +0x52 epilogue)

   Loop structure: two iterations of +0x26..+0x44 (s4 = 30 then 21; the
   bne at +0x42 compares against s5 = 12).  Each iteration either
   descends (V=1) or grafts (kalloc+memset+sd, rejoining at +0x40).
   NO fuel/Löb needed: unroll both iterations, 2x2 = 4 path shapes plus
   the two kalloc-null exits.                                            *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes KernelText.
Require Import WpDecode WpDecodeBridge WpRvcBridge.
Require Import WpMmodeLeafBase.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Import Defs.

Section WalkInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Local Notation WLK off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.walk + off) : mword 64) rvc ast).
  Local Notation csdsp_imm u :=
    (zero_extend' 12 (concat_vec (mword_of_int u : mword 6) ('b"000"))) (only parsing).

  (* the two ExecuteAs redirects not in WpMmodeLeafBase (Local copies,
     as in WpUartPutcSync) *)
  
  Lemma wdec_16 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x89ae : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 19), Regidx (mword_of_int 11)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma wdec_1e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x4a79 : mword 16)) s
    = Some (C_LI (mword_of_int 30, Regidx (mword_of_int 20)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma wdec_20 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x4ab1 : mword 16)) s
    = Some (C_LI (mword_of_int 12, Regidx (mword_of_int 21)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma wdec_2e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x090e : mword 16)) s
    = Some (C_SLLI (mword_of_int 3, Regidx (mword_of_int 18)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma wdec_30 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x9926 : mword 16)) s
    = Some (C_ADD (Regidx (mword_of_int 18), Regidx (mword_of_int 9)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma wdec_3a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xcf85 : mword 16)) s
    = Some (C_BEQZ (mword_of_int 28, Cregidx (mword_of_int 7)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma wdec_3c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x80a9 : mword 16)) s
    = Some (C_SRLI (mword_of_int 10, Cregidx (mword_of_int 1)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma wdec_3e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x04b2 : mword 16)) s
    = Some (C_SLLI (mword_of_int 12, Regidx (mword_of_int 9)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma wdec_40 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x3a5d : mword 16)) s
    = Some (C_ADDIW (mword_of_int 55, Regidx (mword_of_int 20)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma wdec_4e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x050e : mword 16)) s
    = Some (C_SLLI (mword_of_int 3, Regidx (mword_of_int 10)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma wdec_50 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x9526 : mword 16)) s
    = Some (C_ADD (Regidx (mword_of_int 10), Regidx (mword_of_int 9)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  
  Lemma wdec_7c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xd979 : mword 16)) s
    = Some (C_BEQZ (mword_of_int 235, Cregidx (mword_of_int 2)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma wdec_94 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xb775 : mword 16)) s
    = Some (C_J (mword_of_int 2006 : mword 11), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma wdec_98 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xbf6d : mword 16)) s
    = Some (C_J (mword_of_int 2013 : mword 11), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  (* ---- base decode facts (concrete-state bridge) ---- *)
  Lemma wdec_22 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x04b7e263 : mword 32)) s
    = Some (BTYPE (mword_of_int 68 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BLTU), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma wdec_26 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x0149d933 : mword 32)) s
    = Some (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 19), Regidx (mword_of_int 18), SRL), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma wdec_2a s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x1ff97913 : mword 32)) s
    = Some (ITYPE (mword_of_int 511 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ANDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma wdec_32 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00093483 : mword 32)) s
    = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 9), false, 8), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma wdec_36 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x0014f793 : mword 32)) s
    = Some (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), ANDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma wdec_42 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xff5a12e3 : mword 32)) s
    = Some (BTYPE (mword_of_int 8164 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 20), BNE), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma wdec_46 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00c9d513 : mword 32)) s
    = Some (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 19), Regidx (mword_of_int 10), SRLI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma wdec_4a s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x1ff57513 : mword 32)) s
    = Some (ITYPE (mword_of_int 511 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ANDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma wdec_72 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x020b0263 : mword 32)) s
    = Some (BTYPE (mword_of_int 36 : mword 13, zreg, Regidx (mword_of_int 22), BEQ), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma wdec_76 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xb5dff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2095964 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma wdec_82 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xcebff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2096362 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma wdec_86 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00c4d793 : mword 32)) s
    = Some (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 15), SRLI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma wdec_8c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x0017e793 : mword 32)) s
    = Some (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ORI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma wdec_90 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00f93023 : mword 32)) s
    = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 18), 8), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  (* ---- the [instr] catalog ---- *)
  Lemma wi_00 : WLK 0x00 true (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.walk + 0x00)%Z (mword_of_int 0x7139 : mword 16) (mword_of_int (KernelSyms.walk + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)) cdec_7139 exec_execute_C_ADDI16SP. Qed.
  Lemma wi_02 : WLK 0x02 true (STORE (csdsp_imm 7, Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x02)%Z (mword_of_int 0xfc06 : mword 16) (mword_of_int (KernelSyms.walk + 0x02) : mword 64) (STORE (csdsp_imm 7, Regidx (mword_of_int 1), sp, 8)) cdec_fc06 exec_execute_C_SDSP. Qed.
  Lemma wi_04 : WLK 0x04 true (STORE (csdsp_imm 6, Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x04)%Z (mword_of_int 0xf822 : mword 16) (mword_of_int (KernelSyms.walk + 0x04) : mword 64) (STORE (csdsp_imm 6, Regidx (mword_of_int 8), sp, 8)) cdec_f822 exec_execute_C_SDSP. Qed.
  Lemma wi_06 : WLK 0x06 true (STORE (csdsp_imm 5, Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x06)%Z (mword_of_int 0xf426 : mword 16) (mword_of_int (KernelSyms.walk + 0x06) : mword 64) (STORE (csdsp_imm 5, Regidx (mword_of_int 9), sp, 8)) cdec_f426 exec_execute_C_SDSP. Qed.
  Lemma wi_08 : WLK 0x08 true (STORE (csdsp_imm 4, Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x08)%Z (mword_of_int 0xf04a : mword 16) (mword_of_int (KernelSyms.walk + 0x08) : mword 64) (STORE (csdsp_imm 4, Regidx (mword_of_int 18), sp, 8)) cdec_f04a exec_execute_C_SDSP. Qed.
  Lemma wi_0a : WLK 0x0a true (STORE (csdsp_imm 3, Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x0a)%Z (mword_of_int 0xec4e : mword 16) (mword_of_int (KernelSyms.walk + 0x0a) : mword 64) (STORE (csdsp_imm 3, Regidx (mword_of_int 19), sp, 8)) cdec_ec4e exec_execute_C_SDSP. Qed.
  Lemma wi_0c : WLK 0x0c true (STORE (csdsp_imm 2, Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x0c)%Z (mword_of_int 0xe852 : mword 16) (mword_of_int (KernelSyms.walk + 0x0c) : mword 64) (STORE (csdsp_imm 2, Regidx (mword_of_int 20), sp, 8)) cdec_e852 exec_execute_C_SDSP. Qed.
  Lemma wi_0e : WLK 0x0e true (STORE (csdsp_imm 1, Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x0e)%Z (mword_of_int 0xe456 : mword 16) (mword_of_int (KernelSyms.walk + 0x0e) : mword 64) (STORE (csdsp_imm 1, Regidx (mword_of_int 21), sp, 8)) cdec_e456 exec_execute_C_SDSP. Qed.
  Lemma wi_10 : WLK 0x10 true (STORE (csdsp_imm 0, Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x10)%Z (mword_of_int 0xe05a : mword 16) (mword_of_int (KernelSyms.walk + 0x10) : mword 64) (STORE (csdsp_imm 0, Regidx (mword_of_int 22), sp, 8)) cdec_e05a exec_execute_C_SDSP. Qed.
  Lemma wi_12 : WLK 0x12 true (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.walk + 0x12)%Z (mword_of_int 0x0080 : mword 16) (mword_of_int (KernelSyms.walk + 0x12) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0080 exec_execute_C_ADDI4SPN. Qed.
  Lemma wi_14 : WLK 0x14 true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.walk + 0x14)%Z (mword_of_int 0x84aa : mword 16) (mword_of_int (KernelSyms.walk + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.
  Lemma wi_16 : WLK 0x16 true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (KernelSyms.walk + 0x16)%Z (mword_of_int 0x89ae : mword 16) (mword_of_int (KernelSyms.walk + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 19), ADD)) wdec_16 exec_execute_C_MV. Qed.
  Lemma wi_18 : WLK 0x18 true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 22), ADD)).
  Proof. mk_rvc (KernelSyms.walk + 0x18)%Z (mword_of_int 0x8b32 : mword 16) (mword_of_int (KernelSyms.walk + 0x18) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 22), ADD)) cdec_8b32 exec_execute_C_MV. Qed.
  Lemma wi_1a : WLK 0x1a true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (KernelSyms.walk + 0x1a)%Z (mword_of_int 0x57fd : mword 16) (mword_of_int (KernelSyms.walk + 0x1a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_57fd exec_execute_C_LI. Qed.
  Lemma wi_1c : WLK 0x1c true (SHIFTIOP (mword_of_int 26 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)).
  Proof. mk_rvc (KernelSyms.walk + 0x1c)%Z (mword_of_int 0x83e9 : mword 16) (mword_of_int (KernelSyms.walk + 0x1c) : mword 64) (SHIFTIOP (mword_of_int 26 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)) cdec_83e9 exec_execute_C_SRLI. Qed.
  Lemma wi_1e : WLK 0x1e true (ITYPE (sign_extend' 12 (mword_of_int 30 : mword 6), zreg, Regidx (mword_of_int 20), ADDI)).
  Proof. mk_rvc (KernelSyms.walk + 0x1e)%Z (mword_of_int 0x4a79 : mword 16) (mword_of_int (KernelSyms.walk + 0x1e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 30 : mword 6), zreg, Regidx (mword_of_int 20), ADDI)) wdec_1e exec_execute_C_LI. Qed.
  Lemma wi_20 : WLK 0x20 true (ITYPE (sign_extend' 12 (mword_of_int 12 : mword 6), zreg, Regidx (mword_of_int 21), ADDI)).
  Proof. mk_rvc (KernelSyms.walk + 0x20)%Z (mword_of_int 0x4ab1 : mword 16) (mword_of_int (KernelSyms.walk + 0x20) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 12 : mword 6), zreg, Regidx (mword_of_int 21), ADDI)) wdec_20 exec_execute_C_LI. Qed.
  Lemma wi_2e : WLK 0x2e true (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 18), Regidx (mword_of_int 18), SLLI)).
  Proof. mk_rvc (KernelSyms.walk + 0x2e)%Z (mword_of_int 0x090e : mword 16) (mword_of_int (KernelSyms.walk + 0x2e) : mword 64) (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 18), Regidx (mword_of_int 18), SLLI)) wdec_2e exec_execute_C_SLLI. Qed.
  Lemma wi_30 : WLK 0x30 true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (KernelSyms.walk + 0x30)%Z (mword_of_int 0x9926 : mword 16) (mword_of_int (KernelSyms.walk + 0x30) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)) wdec_30 exec_execute_C_ADD. Qed.
  Lemma wi_3a : WLK 0x3a true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (KernelSyms.walk + 0x3a)%Z (mword_of_int 0xcf85 : mword 16) (mword_of_int (KernelSyms.walk + 0x3a) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) wdec_3a exec_execute_C_BEQZ. Qed.
  Lemma wi_3c : WLK 0x3c true (SHIFTIOP (mword_of_int 10 : mword 6, creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 1)), SRLI)).
  Proof. mk_rvc (KernelSyms.walk + 0x3c)%Z (mword_of_int 0x80a9 : mword 16) (mword_of_int (KernelSyms.walk + 0x3c) : mword 64) (SHIFTIOP (mword_of_int 10 : mword 6, creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 1)), SRLI)) wdec_3c exec_execute_C_SRLI. Qed.
  Lemma wi_3e : WLK 0x3e true (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 9), SLLI)).
  Proof. mk_rvc (KernelSyms.walk + 0x3e)%Z (mword_of_int 0x04b2 : mword 16) (mword_of_int (KernelSyms.walk + 0x3e) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 9), SLLI)) wdec_3e exec_execute_C_SLLI. Qed.
  Lemma wi_40 : WLK 0x40 true (ADDIW (sign_extend' 12 (mword_of_int 55 : mword 6), Regidx (mword_of_int 20), Regidx (mword_of_int 20))).
  Proof. mk_rvc (KernelSyms.walk + 0x40)%Z (mword_of_int 0x3a5d : mword 16) (mword_of_int (KernelSyms.walk + 0x40) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 55 : mword 6), Regidx (mword_of_int 20), Regidx (mword_of_int 20))) wdec_40 exec_execute_C_ADDIW. Qed.
  Lemma wi_4e : WLK 0x4e true (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLLI)).
  Proof. mk_rvc (KernelSyms.walk + 0x4e)%Z (mword_of_int 0x050e : mword 16) (mword_of_int (KernelSyms.walk + 0x4e) : mword 64) (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLLI)) wdec_4e exec_execute_C_SLLI. Qed.
  Lemma wi_50 : WLK 0x50 true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.walk + 0x50)%Z (mword_of_int 0x9526 : mword 16) (mword_of_int (KernelSyms.walk + 0x50) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)) wdec_50 exec_execute_C_ADD. Qed.
  Lemma wi_52 : WLK 0x52 true (LOAD (csdsp_imm 7, sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x52)%Z (mword_of_int 0x70e2 : mword 16) (mword_of_int (KernelSyms.walk + 0x52) : mword 64) (LOAD (csdsp_imm 7, sp, Regidx (mword_of_int 1), false, 8)) cdec_70e2 exec_execute_C_LDSP. Qed.
  Lemma wi_54 : WLK 0x54 true (LOAD (csdsp_imm 6, sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x54)%Z (mword_of_int 0x7442 : mword 16) (mword_of_int (KernelSyms.walk + 0x54) : mword 64) (LOAD (csdsp_imm 6, sp, Regidx (mword_of_int 8), false, 8)) cdec_7442 exec_execute_C_LDSP. Qed.
  Lemma wi_56 : WLK 0x56 true (LOAD (csdsp_imm 5, sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x56)%Z (mword_of_int 0x74a2 : mword 16) (mword_of_int (KernelSyms.walk + 0x56) : mword 64) (LOAD (csdsp_imm 5, sp, Regidx (mword_of_int 9), false, 8)) cdec_74a2 exec_execute_C_LDSP. Qed.
  Lemma wi_58 : WLK 0x58 true (LOAD (csdsp_imm 4, sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x58)%Z (mword_of_int 0x7902 : mword 16) (mword_of_int (KernelSyms.walk + 0x58) : mword 64) (LOAD (csdsp_imm 4, sp, Regidx (mword_of_int 18), false, 8)) cdec_7902 exec_execute_C_LDSP. Qed.
  Lemma wi_5a : WLK 0x5a true (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x5a)%Z (mword_of_int 0x69e2 : mword 16) (mword_of_int (KernelSyms.walk + 0x5a) : mword 64) (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 19), false, 8)) cdec_69e2 exec_execute_C_LDSP. Qed.
  Lemma wi_5c : WLK 0x5c true (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x5c)%Z (mword_of_int 0x6a42 : mword 16) (mword_of_int (KernelSyms.walk + 0x5c) : mword 64) (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 20), false, 8)) cdec_6a42 exec_execute_C_LDSP. Qed.
  Lemma wi_5e : WLK 0x5e true (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x5e)%Z (mword_of_int 0x6aa2 : mword 16) (mword_of_int (KernelSyms.walk + 0x5e) : mword 64) (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 21), false, 8)) cdec_6aa2 exec_execute_C_LDSP. Qed.
  Lemma wi_60 : WLK 0x60 true (LOAD (csdsp_imm 0, sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (KernelSyms.walk + 0x60)%Z (mword_of_int 0x6b02 : mword 16) (mword_of_int (KernelSyms.walk + 0x60) : mword 64) (LOAD (csdsp_imm 0, sp, Regidx (mword_of_int 22), false, 8)) cdec_6b02 exec_execute_C_LDSP. Qed.
  Lemma wi_62 : WLK 0x62 true (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.walk + 0x62)%Z (mword_of_int 0x6121 : mword 16) (mword_of_int (KernelSyms.walk + 0x62) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)) cdec_6121 exec_execute_C_ADDI16SP. Qed.
  Lemma wi_64 : WLK 0x64 true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.walk + 0x64)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int (KernelSyms.walk + 0x64) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.
  Lemma wi_7c : WLK 0x7c true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 235 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (KernelSyms.walk + 0x7c)%Z (mword_of_int 0xd979 : mword 16) (mword_of_int (KernelSyms.walk + 0x7c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 235 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) wdec_7c exec_execute_C_BEQZ. Qed.
  Lemma wi_7e : WLK 0x7e true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)).
  Proof. mk_rvc (KernelSyms.walk + 0x7e)%Z (mword_of_int 0x6605 : mword 16) (mword_of_int (KernelSyms.walk + 0x7e) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)) cdec_6605 exec_execute_C_LUI. Qed.
  Lemma wi_80 : WLK 0x80 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (KernelSyms.walk + 0x80)%Z (mword_of_int 0x4581 : mword 16) (mword_of_int (KernelSyms.walk + 0x80) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4581 exec_execute_C_LI. Qed.
  Lemma wi_8a : WLK 0x8a true (SHIFTIOP (mword_of_int 10 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (KernelSyms.walk + 0x8a)%Z (mword_of_int 0x07aa : mword 16) (mword_of_int (KernelSyms.walk + 0x8a) : mword 64) (SHIFTIOP (mword_of_int 10 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) cdec_07aa exec_execute_C_SLLI. Qed.
  Lemma wi_94 : WLK 0x94 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.walk + 0x94)%Z (mword_of_int 0xb775 : mword 16) (mword_of_int (KernelSyms.walk + 0x94) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0")), zreg)) wdec_94 exec_execute_C_J. Qed.
  (* the alloc = 0 arm (+0x96/+0x98): dead under the alloc = 1 premise, live
     for walk(_,_,0) -- ProofWalkNoalloc's path. *)
  Lemma wi_96 : WLK 0x96 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KernelSyms.walk + 0x96)%Z (mword_of_int 0x4501 : mword 16) (mword_of_int (KernelSyms.walk + 0x96) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.
  Lemma wi_98 : WLK 0x98 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2013 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.walk + 0x98)%Z (mword_of_int 0xbf6d : mword 16) (mword_of_int (KernelSyms.walk + 0x98) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2013 : mword 11) ('b"0")), zreg)) wdec_98 exec_execute_C_J. Qed.
  Lemma wi_7a : WLK 0x7a true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.walk + 0x7a)%Z (mword_of_int 0x84aa : mword 16) (mword_of_int (KernelSyms.walk + 0x7a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.
  Lemma wi_22 : WLK 0x22 false (BTYPE (mword_of_int 68 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BLTU)).
  Proof. mk_base (KernelSyms.walk + 0x22)%Z (mword_of_int 0x04b7e263 : mword 32) (mword_of_int (KernelSyms.walk + 0x22) : mword 64) (BTYPE (mword_of_int 68 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BLTU)) wdec_22. Qed.
  Lemma wi_26 : WLK 0x26 false (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 19), Regidx (mword_of_int 18), SRL)).
  Proof. mk_base (KernelSyms.walk + 0x26)%Z (mword_of_int 0x0149d933 : mword 32) (mword_of_int (KernelSyms.walk + 0x26) : mword 64) (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 19), Regidx (mword_of_int 18), SRL)) wdec_26. Qed.
  Lemma wi_2a : WLK 0x2a false (ITYPE (mword_of_int 511 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ANDI)).
  Proof. mk_base (KernelSyms.walk + 0x2a)%Z (mword_of_int 0x1ff97913 : mword 32) (mword_of_int (KernelSyms.walk + 0x2a) : mword 64) (ITYPE (mword_of_int 511 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ANDI)) wdec_2a. Qed.
  Lemma wi_32 : WLK 0x32 false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 9), false, 8)).
  Proof. mk_base (KernelSyms.walk + 0x32)%Z (mword_of_int 0x00093483 : mword 32) (mword_of_int (KernelSyms.walk + 0x32) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 9), false, 8)) wdec_32. Qed.
  Lemma wi_36 : WLK 0x36 false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_base (KernelSyms.walk + 0x36)%Z (mword_of_int 0x0014f793 : mword 32) (mword_of_int (KernelSyms.walk + 0x36) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), ANDI)) wdec_36. Qed.
  Lemma wi_42 : WLK 0x42 false (BTYPE (mword_of_int 8164 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 20), BNE)).
  Proof. mk_base (KernelSyms.walk + 0x42)%Z (mword_of_int 0xff5a12e3 : mword 32) (mword_of_int (KernelSyms.walk + 0x42) : mword 64) (BTYPE (mword_of_int 8164 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 20), BNE)) wdec_42. Qed.
  Lemma wi_46 : WLK 0x46 false (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 19), Regidx (mword_of_int 10), SRLI)).
  Proof. mk_base (KernelSyms.walk + 0x46)%Z (mword_of_int 0x00c9d513 : mword 32) (mword_of_int (KernelSyms.walk + 0x46) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 19), Regidx (mword_of_int 10), SRLI)) wdec_46. Qed.
  Lemma wi_4a : WLK 0x4a false (ITYPE (mword_of_int 511 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ANDI)).
  Proof. mk_base (KernelSyms.walk + 0x4a)%Z (mword_of_int 0x1ff57513 : mword 32) (mword_of_int (KernelSyms.walk + 0x4a) : mword 64) (ITYPE (mword_of_int 511 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ANDI)) wdec_4a. Qed.
  Lemma wi_72 : WLK 0x72 false (BTYPE (mword_of_int 36 : mword 13, zreg, Regidx (mword_of_int 22), BEQ)).
  Proof. mk_base (KernelSyms.walk + 0x72)%Z (mword_of_int 0x020b0263 : mword 32) (mword_of_int (KernelSyms.walk + 0x72) : mword 64) (BTYPE (mword_of_int 36 : mword 13, zreg, Regidx (mword_of_int 22), BEQ)) wdec_72. Qed.
  Lemma wi_76 : WLK 0x76 false (JAL (mword_of_int 2095964 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.walk + 0x76)%Z (mword_of_int 0xb5dff0ef : mword 32) (mword_of_int (KernelSyms.walk + 0x76) : mword 64) (JAL (mword_of_int 2095964 : mword 21, Regidx (mword_of_int 1))) wdec_76. Qed.
  Lemma wi_82 : WLK 0x82 false (JAL (mword_of_int 2096362 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.walk + 0x82)%Z (mword_of_int 0xcebff0ef : mword 32) (mword_of_int (KernelSyms.walk + 0x82) : mword 64) (JAL (mword_of_int 2096362 : mword 21, Regidx (mword_of_int 1))) wdec_82. Qed.
  Lemma wi_86 : WLK 0x86 false (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 15), SRLI)).
  Proof. mk_base (KernelSyms.walk + 0x86)%Z (mword_of_int 0x00c4d793 : mword 32) (mword_of_int (KernelSyms.walk + 0x86) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 15), SRLI)) wdec_86. Qed.
  Lemma wi_8c : WLK 0x8c false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ORI)).
  Proof. mk_base (KernelSyms.walk + 0x8c)%Z (mword_of_int 0x0017e793 : mword 32) (mword_of_int (KernelSyms.walk + 0x8c) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ORI)) wdec_8c. Qed.
  Lemma wi_90 : WLK 0x90 false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 18), 8)).
  Proof. mk_base (KernelSyms.walk + 0x90)%Z (mword_of_int 0x00f93023 : mword 32) (mword_of_int (KernelSyms.walk + 0x90) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 18), 8)) wdec_90. Qed.
End WalkInstrs.
