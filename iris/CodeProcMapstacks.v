(* CodeProcMapstacks.v -- decode catalog for xv6's proc_mapstacks()
   (kernel/proc.c).  Per-instruction decode facts [pmsdec_] + [instr]
   constructors [pmsi_], consumed by the wp_proc_mapstacks proof; same
   architecture as CodeMappages.v / CodeWalk.v.

   Function body = KernelInstrs.v bytes at KernelSyms.proc_mapstacks
   (0x80001776 .. 0x8000181a, 62 instrs).  Frame 0x715d = addi sp,sp,-80
   (80 bytes = 10 saved-register slots: ra,s0..s8 at 72..0).  The KSTACK
   address arithmetic (auipc/lui/addi/slli, mul-by-stride, sub), the
   proc-array stride 0x168 = 360 (addi s1,s1,360 @ +0x78), the kalloc +
   kvmmap jals (JAL residues = (target - pc) mod 2^21), the p < &proc[NPROC]
   loop bne @ +0x7c, and the kalloc-null panic branch (beqz @ +0x58 -> the
   auipc/addi/jal panic @ +0x98..+0xa0) are all catalogued.  Immediates and
   ASTs are the exact vm_compute-on-decode outputs against the reference
   config state. *)
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
Require Import ExecCommon.
From Kernel Require KernelSyms.
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
Import Defs.

Section ProcMapstacksInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Local Notation PMS off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.proc_mapstacks + off) : mword 64) rvc ast).
  Local Notation csdsp_imm u :=
    (zero_extend' 12 (concat_vec (mword_of_int u : mword 6) ('b"000"))) (only parsing).

  (* ExecuteAs redirects not in WpMmodeLeafBase (Local copies, as in
     CodeMappages / CodeWalk) *)
  (* [cdec_e062] (+0x14, c.sdsp s8,0(sp)) -- shared, see KernelRvcDecode.v *)
  Lemma pmsdec_1e s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xfe848493 : mword 32)) s
    = Some (ITYPE (mword_of_int 4072 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pmsdec_22 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x8c26 : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 24), Regidx (mword_of_int 9)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  
  
  
  
  
  
  
  
  
  Lemma pmsdec_46 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x4b99 : mword 16)) s
    = Some (C_LI (mword_of_int 6, Regidx (mword_of_int 23)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pmsdec_4a s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00017a97 : mword 32)) s
    = Some (UTYPE (mword_of_int 23 : mword 20, Regidx (mword_of_int 21), AUIPC), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pmsdec_4e s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x9b8a8a93 : mword 32)) s
    = Some (ITYPE (mword_of_int 2488 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pmsdec_52 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xb66ff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2093926 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  (* 0x862a  c.mv a2,a0 -- shared with fdalloc, so [cdec_862a]
     (KernelRvcDecode.v) *)
  Lemma pmsdec_5a s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x418485b3 : mword 32)) s
    = Some (RTYPE (Regidx (mword_of_int 24), Regidx (mword_of_int 9), Regidx (mword_of_int 11), SUB), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pmsdec_5e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x858d : mword 16)) s
    = Some (C_SRAI (mword_of_int 3, Cregidx (mword_of_int 3)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pmsdec_60 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x032585b3 : mword 32)) s
    = Some (MUL (Regidx (mword_of_int 18), Regidx (mword_of_int 11), Regidx (mword_of_int 11), mulop_mul), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pmsdec_66 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6789 : mword 16)) s
    = Some (C_LUI (mword_of_int 2, Regidx (mword_of_int 15)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pmsdec_68 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x9dbd : mword 16)) s
    = Some (C_ADDW (Cregidx (mword_of_int 3), Cregidx (mword_of_int 7)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pmsdec_6a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x875e : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 14), Regidx (mword_of_int 23)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pmsdec_6c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x86da : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 13), Regidx (mword_of_int 22)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pmsdec_6e s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x40b985b3 : mword 32)) s
    = Some (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 19), Regidx (mword_of_int 11), SUB), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pmsdec_74 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x8fdff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2095356 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  
  Lemma pmsdec_7c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xfd549be3 : mword 32)) s
    = Some (BTYPE (mword_of_int 8150 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 9), BNE), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pmsdec_92 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6c02 : mword 16)) s
    = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 24)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  (* [bdec_00006517] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)
  Lemma pmsdec_9c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x94a50513 : mword 32)) s
    = Some (ITYPE (mword_of_int 2378 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

  (* ---- instr lemmas ---- *)
  Lemma pmsi_00 : PMS 0x00 true (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)).  (*  *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x00)%Z (mword_of_int 0x715d : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)) cdec_715d exec_execute_C_ADDI16SP. Qed.
  Lemma pmsi_02 : PMS 0x02 true (STORE (csdsp_imm 9, Regidx (mword_of_int 1), sp, 8)).  (* sd ra,72(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x02)%Z (mword_of_int 0xe486 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x02) : mword 64) (STORE (csdsp_imm 9, Regidx (mword_of_int 1), sp, 8)) cdec_e486 exec_execute_C_SDSP. Qed.
  Lemma pmsi_04 : PMS 0x04 true (STORE (csdsp_imm 8, Regidx (mword_of_int 8), sp, 8)).  (* sd s0,64(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x04)%Z (mword_of_int 0xe0a2 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x04) : mword 64) (STORE (csdsp_imm 8, Regidx (mword_of_int 8), sp, 8)) cdec_e0a2 exec_execute_C_SDSP. Qed.
  Lemma pmsi_06 : PMS 0x06 true (STORE (csdsp_imm 7, Regidx (mword_of_int 9), sp, 8)).  (* sd s1,56(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x06)%Z (mword_of_int 0xfc26 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x06) : mword 64) (STORE (csdsp_imm 7, Regidx (mword_of_int 9), sp, 8)) cdec_fc26 exec_execute_C_SDSP. Qed.
  Lemma pmsi_08 : PMS 0x08 true (STORE (csdsp_imm 6, Regidx (mword_of_int 18), sp, 8)).  (* sd s2,48(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x08)%Z (mword_of_int 0xf84a : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x08) : mword 64) (STORE (csdsp_imm 6, Regidx (mword_of_int 18), sp, 8)) cdec_f84a exec_execute_C_SDSP. Qed.
  Lemma pmsi_0a : PMS 0x0a true (STORE (csdsp_imm 5, Regidx (mword_of_int 19), sp, 8)).  (* sd s3,40(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x0a)%Z (mword_of_int 0xf44e : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x0a) : mword 64) (STORE (csdsp_imm 5, Regidx (mword_of_int 19), sp, 8)) cdec_f44e exec_execute_C_SDSP. Qed.
  Lemma pmsi_0c : PMS 0x0c true (STORE (csdsp_imm 4, Regidx (mword_of_int 20), sp, 8)).  (* sd s4,32(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x0c)%Z (mword_of_int 0xf052 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x0c) : mword 64) (STORE (csdsp_imm 4, Regidx (mword_of_int 20), sp, 8)) cdec_f052 exec_execute_C_SDSP. Qed.
  Lemma pmsi_0e : PMS 0x0e true (STORE (csdsp_imm 3, Regidx (mword_of_int 21), sp, 8)).  (* sd s5,24(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x0e)%Z (mword_of_int 0xec56 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x0e) : mword 64) (STORE (csdsp_imm 3, Regidx (mword_of_int 21), sp, 8)) cdec_ec56 exec_execute_C_SDSP. Qed.
  Lemma pmsi_10 : PMS 0x10 true (STORE (csdsp_imm 2, Regidx (mword_of_int 22), sp, 8)).  (* sd s6,16(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x10)%Z (mword_of_int 0xe85a : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x10) : mword 64) (STORE (csdsp_imm 2, Regidx (mword_of_int 22), sp, 8)) cdec_e85a exec_execute_C_SDSP. Qed.
  Lemma pmsi_12 : PMS 0x12 true (STORE (csdsp_imm 1, Regidx (mword_of_int 23), sp, 8)).  (* sd s7,8(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x12)%Z (mword_of_int 0xe45e : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x12) : mword 64) (STORE (csdsp_imm 1, Regidx (mword_of_int 23), sp, 8)) cdec_e45e exec_execute_C_SDSP. Qed.
  Lemma pmsi_14 : PMS 0x14 true (STORE (csdsp_imm 0, Regidx (mword_of_int 24), sp, 8)).  (* sd s8,0(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x14)%Z (mword_of_int 0xe062 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x14) : mword 64) (STORE (csdsp_imm 0, Regidx (mword_of_int 24), sp, 8)) cdec_e062 exec_execute_C_SDSP. Qed.
  Lemma pmsi_16 : PMS 0x16 true (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).  (* addi s0,sp,80 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x16)%Z (mword_of_int 0x0880 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x16) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0880 exec_execute_C_ADDI4SPN. Qed.
  Lemma pmsi_18 : PMS 0x18 true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)).  (* mv s4,a0 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x18)%Z (mword_of_int 0x8a2a : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x18) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)) cdec_8a2a exec_execute_C_MV. Qed.
  Lemma pmsi_1a : PMS 0x1a false (UTYPE (mword_of_int 17 : mword 20, Regidx (mword_of_int 9), AUIPC)).  (* auipc s1,0x11 *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x1a)%Z (mword_of_int 0x00011497 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x1a) : mword 64) (UTYPE (mword_of_int 17 : mword 20, Regidx (mword_of_int 9), AUIPC)) bdec_00011497. Qed.
  Lemma pmsi_1e : PMS 0x1e false (ITYPE (mword_of_int 4072 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).  (* addi s1,s1,-24 # 80012778 <proc> *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x1e)%Z (mword_of_int 0xfe848493 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x1e) : mword 64) (ITYPE (mword_of_int 4072 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) pmsdec_1e. Qed.
  Lemma pmsi_22 : PMS 0x22 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 24), ADD)).  (* mv s8,s1 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x22)%Z (mword_of_int 0x8c26 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x22) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 24), ADD)) pmsdec_22 exec_execute_C_MV. Qed.
  Lemma pmsi_24 : PMS 0x24 false (UTYPE (mword_of_int 165 : mword 20, Regidx (mword_of_int 15), LUI)).  (* lui a5,0xa5 *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x24)%Z (mword_of_int 0x000a57b7 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x24) : mword 64) (UTYPE (mword_of_int 165 : mword 20, Regidx (mword_of_int 15), LUI)) bdec_000a57b7. Qed.
  Lemma pmsi_28 : PMS 0x28 false (ITYPE (mword_of_int 4005 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).  (* addi a5,a5,-91 # a4fa5 <_entry-0x7ff5b05b> *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x28)%Z (mword_of_int 0xfa578793 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x28) : mword 64) (ITYPE (mword_of_int 4005 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) bdec_fa578793. Qed.
  Lemma pmsi_2c : PMS 0x2c true (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).  (* slli a5,a5,0xc *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x2c)%Z (mword_of_int 0x07b2 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x2c) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) cdec_07b2 exec_execute_C_SLLI. Qed.
  Lemma pmsi_2e : PMS 0x2e false (ITYPE (mword_of_int 4005 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).  (* addi a5,a5,-91 *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x2e)%Z (mword_of_int 0xfa578793 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x2e) : mword 64) (ITYPE (mword_of_int 4005 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) bdec_fa578793. Qed.
  Lemma pmsi_32 : PMS 0x32 false (UTYPE (mword_of_int 326224 : mword 20, Regidx (mword_of_int 18), LUI)).  (* lui s2,0x4fa50 *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x32)%Z (mword_of_int 0x4fa50937 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x32) : mword 64) (UTYPE (mword_of_int 326224 : mword 20, Regidx (mword_of_int 18), LUI)) bdec_4fa50937. Qed.
  Lemma pmsi_36 : PMS 0x36 false (ITYPE (mword_of_int 2639 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).  (* addi s2,s2,-1457 # 4fa4fa4f <_entry-0x305b05b1> *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x36)%Z (mword_of_int 0xa4f90913 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x36) : mword 64) (ITYPE (mword_of_int 2639 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) bdec_a4f90913. Qed.
  Lemma pmsi_3a : PMS 0x3a true (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 18), Regidx (mword_of_int 18), SLLI)).  (* slli s2,s2,0x20 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x3a)%Z (mword_of_int 0x1902 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x3a) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 18), Regidx (mword_of_int 18), SLLI)) cdec_1902 exec_execute_C_SLLI. Qed.
  Lemma pmsi_3c : PMS 0x3c true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)).  (* add s2,s2,a5 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x3c)%Z (mword_of_int 0x993e : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x3c) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)) cdec_993e exec_execute_C_ADD. Qed.
  Lemma pmsi_3e : PMS 0x3e false (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 19), LUI)).  (* lui s3,0x4000 *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x3e)%Z (mword_of_int 0x040009b7 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x3e) : mword 64) (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 19), LUI)) bdec_040009b7. Qed.
  Lemma pmsi_42 : PMS 0x42 true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI)).  (* addi s3,s3,-1 # 3ffffff <_entry-0x7c000001> *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x42)%Z (mword_of_int 0x19fd : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x42) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI)) cdec_19fd exec_execute_C_ADDI. Qed.
  Lemma pmsi_44 : PMS 0x44 true (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 19), Regidx (mword_of_int 19), SLLI)).  (* slli s3,s3,0xc *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x44)%Z (mword_of_int 0x09b2 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x44) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 19), Regidx (mword_of_int 19), SLLI)) cdec_09b2 exec_execute_C_SLLI. Qed.
  Lemma pmsi_46 : PMS 0x46 true (ITYPE (sign_extend' 12 (mword_of_int 6 : mword 6), zreg, Regidx (mword_of_int 23), ADDI)).  (* li s7,6 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x46)%Z (mword_of_int 0x4b99 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x46) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 6 : mword 6), zreg, Regidx (mword_of_int 23), ADDI)) pmsdec_46 exec_execute_C_LI. Qed.
  Lemma pmsi_48 : PMS 0x48 true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 22), LUI)).  (* lui s6,0x1 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x48)%Z (mword_of_int 0x6b05 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x48) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 22), LUI)) cdec_6b05 exec_execute_C_LUI. Qed.
  Lemma pmsi_4a : PMS 0x4a false (UTYPE (mword_of_int 23 : mword 20, Regidx (mword_of_int 21), AUIPC)).  (* auipc s5,0x17 *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x4a)%Z (mword_of_int 0x00017a97 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x4a) : mword 64) (UTYPE (mword_of_int 23 : mword 20, Regidx (mword_of_int 21), AUIPC)) pmsdec_4a. Qed.
  Lemma pmsi_4e : PMS 0x4e false (ITYPE (mword_of_int 2488 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI)).  (* addi s5,s5,-1608 # 80018178 <tickslock> *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x4e)%Z (mword_of_int 0x9b8a8a93 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x4e) : mword 64) (ITYPE (mword_of_int 2488 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI)) pmsdec_4e. Qed.
  Lemma pmsi_52 : PMS 0x52 false (JAL (mword_of_int 2093926 : mword 21, Regidx (mword_of_int 1))).  (* jal 80000b2e <kalloc> *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x52)%Z (mword_of_int 0xb66ff0ef : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x52) : mword 64) (JAL (mword_of_int 2093926 : mword 21, Regidx (mword_of_int 1))) pmsdec_52. Qed.
  Lemma pmsi_56 : PMS 0x56 true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 12), ADD)).  (* mv a2,a0 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x56)%Z (mword_of_int 0x862a : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x56) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 12), ADD)) cdec_862a exec_execute_C_MV. Qed.
  Lemma pmsi_58 : PMS 0x58 true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 32 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).  (* beqz a0,8000180e <proc_mapstacks+0x98> *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x58)%Z (mword_of_int 0xc121 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x58) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 32 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) cdec_c121 exec_execute_C_BEQZ. Qed.
  Lemma pmsi_5a : PMS 0x5a false (RTYPE (Regidx (mword_of_int 24), Regidx (mword_of_int 9), Regidx (mword_of_int 11), SUB)).  (* sub a1,s1,s8 *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x5a)%Z (mword_of_int 0x418485b3 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x5a) : mword 64) (RTYPE (Regidx (mword_of_int 24), Regidx (mword_of_int 9), Regidx (mword_of_int 11), SUB)) pmsdec_5a. Qed.
  Lemma pmsi_5e : PMS 0x5e true (SHIFTIOP (mword_of_int 3 : mword 6, creg2reg_idx (Cregidx (mword_of_int 3)), creg2reg_idx (Cregidx (mword_of_int 3)), SRAI)).  (* srai a1,a1,0x3 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x5e)%Z (mword_of_int 0x858d : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x5e) : mword 64) (SHIFTIOP (mword_of_int 3 : mword 6, creg2reg_idx (Cregidx (mword_of_int 3)), creg2reg_idx (Cregidx (mword_of_int 3)), SRAI)) pmsdec_5e exec_execute_C_SRAI. Qed.
  Lemma pmsi_60 : PMS 0x60 false (MUL (Regidx (mword_of_int 18), Regidx (mword_of_int 11), Regidx (mword_of_int 11), mulop_mul)).  (* mul a1,a1,s2 *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x60)%Z (mword_of_int 0x032585b3 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x60) : mword 64) (MUL (Regidx (mword_of_int 18), Regidx (mword_of_int 11), Regidx (mword_of_int 11), mulop_mul)) pmsdec_60. Qed.
  Lemma pmsi_64 : PMS 0x64 true (SHIFTIOP (mword_of_int 13 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)).  (* slli a1,a1,0xd *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x64)%Z (mword_of_int 0x05b6 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x64) : mword 64) (SHIFTIOP (mword_of_int 13 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)) cdec_05b6 exec_execute_C_SLLI. Qed.
  Lemma pmsi_66 : PMS 0x66 true (UTYPE (sign_extend' 20 (mword_of_int 2 : mword 6), Regidx (mword_of_int 15), LUI)).  (* lui a5,0x2 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x66)%Z (mword_of_int 0x6789 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x66) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 2 : mword 6), Regidx (mword_of_int 15), LUI)) pmsdec_66 exec_execute_C_LUI. Qed.
  Lemma pmsi_68 : PMS 0x68 true (RTYPEW (creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 3)), creg2reg_idx (Cregidx (mword_of_int 3)), ADDW)).  (* addw a1,a1,a5 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x68)%Z (mword_of_int 0x9dbd : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x68) : mword 64) (RTYPEW (creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 3)), creg2reg_idx (Cregidx (mword_of_int 3)), ADDW)) pmsdec_68 exec_execute_C_ADDW. Qed.
  Lemma pmsi_6a : PMS 0x6a true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 14), ADD)).  (* mv a4,s7 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x6a)%Z (mword_of_int 0x875e : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x6a) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 14), ADD)) pmsdec_6a exec_execute_C_MV. Qed.
  Lemma pmsi_6c : PMS 0x6c true (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 13), ADD)).  (* mv a3,s6 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x6c)%Z (mword_of_int 0x86da : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x6c) : mword 64) (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 13), ADD)) pmsdec_6c exec_execute_C_MV. Qed.
  Lemma pmsi_6e : PMS 0x6e false (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 19), Regidx (mword_of_int 11), SUB)).  (* sub a1,s3,a1 *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x6e)%Z (mword_of_int 0x40b985b3 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x6e) : mword 64) (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 19), Regidx (mword_of_int 11), SUB)) pmsdec_6e. Qed.
  Lemma pmsi_72 : PMS 0x72 true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)).  (* mv a0,s4 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x72)%Z (mword_of_int 0x8552 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x72) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)) cdec_8552 exec_execute_C_MV. Qed.
  Lemma pmsi_74 : PMS 0x74 false (JAL (mword_of_int 2095356 : mword 21, Regidx (mword_of_int 1))).  (* jal 800010e6 <kvmmap> *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x74)%Z (mword_of_int 0x8fdff0ef : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x74) : mword 64) (JAL (mword_of_int 2095356 : mword 21, Regidx (mword_of_int 1))) pmsdec_74. Qed.
  Lemma pmsi_78 : PMS 0x78 false (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).  (* addi s1,s1,360 *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x78)%Z (mword_of_int 0x16848493 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x78) : mword 64) (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) bdec_16848493. Qed.
  Lemma pmsi_7c : PMS 0x7c false (BTYPE (mword_of_int 8150 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 9), BNE)).  (* bne s1,s5,800017c8 <proc_mapstacks+0x52> *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x7c)%Z (mword_of_int 0xfd549be3 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x7c) : mword 64) (BTYPE (mword_of_int 8150 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 9), BNE)) pmsdec_7c. Qed.
  Lemma pmsi_80 : PMS 0x80 true (LOAD (csdsp_imm 9, sp, Regidx (mword_of_int 1), false, 8)).  (* ld ra,72(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x80)%Z (mword_of_int 0x60a6 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x80) : mword 64) (LOAD (csdsp_imm 9, sp, Regidx (mword_of_int 1), false, 8)) cdec_60a6 exec_execute_C_LDSP. Qed.
  Lemma pmsi_82 : PMS 0x82 true (LOAD (csdsp_imm 8, sp, Regidx (mword_of_int 8), false, 8)).  (* ld s0,64(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x82)%Z (mword_of_int 0x6406 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x82) : mword 64) (LOAD (csdsp_imm 8, sp, Regidx (mword_of_int 8), false, 8)) cdec_6406 exec_execute_C_LDSP. Qed.
  Lemma pmsi_84 : PMS 0x84 true (LOAD (csdsp_imm 7, sp, Regidx (mword_of_int 9), false, 8)).  (* ld s1,56(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x84)%Z (mword_of_int 0x74e2 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x84) : mword 64) (LOAD (csdsp_imm 7, sp, Regidx (mword_of_int 9), false, 8)) cdec_74e2 exec_execute_C_LDSP. Qed.
  Lemma pmsi_86 : PMS 0x86 true (LOAD (csdsp_imm 6, sp, Regidx (mword_of_int 18), false, 8)).  (* ld s2,48(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x86)%Z (mword_of_int 0x7942 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x86) : mword 64) (LOAD (csdsp_imm 6, sp, Regidx (mword_of_int 18), false, 8)) cdec_7942 exec_execute_C_LDSP. Qed.
  Lemma pmsi_88 : PMS 0x88 true (LOAD (csdsp_imm 5, sp, Regidx (mword_of_int 19), false, 8)).  (* ld s3,40(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x88)%Z (mword_of_int 0x79a2 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x88) : mword 64) (LOAD (csdsp_imm 5, sp, Regidx (mword_of_int 19), false, 8)) cdec_79a2 exec_execute_C_LDSP. Qed.
  Lemma pmsi_8a : PMS 0x8a true (LOAD (csdsp_imm 4, sp, Regidx (mword_of_int 20), false, 8)).  (* ld s4,32(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x8a)%Z (mword_of_int 0x7a02 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x8a) : mword 64) (LOAD (csdsp_imm 4, sp, Regidx (mword_of_int 20), false, 8)) cdec_7a02 exec_execute_C_LDSP. Qed.
  Lemma pmsi_8c : PMS 0x8c true (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 21), false, 8)).  (* ld s5,24(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x8c)%Z (mword_of_int 0x6ae2 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x8c) : mword 64) (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 21), false, 8)) cdec_6ae2 exec_execute_C_LDSP. Qed.
  Lemma pmsi_8e : PMS 0x8e true (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 22), false, 8)).  (* ld s6,16(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x8e)%Z (mword_of_int 0x6b42 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x8e) : mword 64) (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 22), false, 8)) cdec_6b42 exec_execute_C_LDSP. Qed.
  Lemma pmsi_90 : PMS 0x90 true (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 23), false, 8)).  (* ld s7,8(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x90)%Z (mword_of_int 0x6ba2 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x90) : mword 64) (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 23), false, 8)) cdec_6ba2 exec_execute_C_LDSP. Qed.
  Lemma pmsi_92 : PMS 0x92 true (LOAD (csdsp_imm 0, sp, Regidx (mword_of_int 24), false, 8)).  (* ld s8,0(sp) *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x92)%Z (mword_of_int 0x6c02 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x92) : mword 64) (LOAD (csdsp_imm 0, sp, Regidx (mword_of_int 24), false, 8)) pmsdec_92 exec_execute_C_LDSP. Qed.
  Lemma pmsi_94 : PMS 0x94 true (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)).  (* addi sp,sp,80 *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x94)%Z (mword_of_int 0x6161 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x94) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)) cdec_6161 exec_execute_C_ADDI16SP. Qed.
  Lemma pmsi_96 : PMS 0x96 true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* ret *)
  Proof. mk_rvc (KernelSyms.proc_mapstacks + 0x96)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int (KernelSyms.proc_mapstacks + 0x96) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.
  Lemma pmsi_98 : PMS 0x98 false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)).  (* auipc a0,0x6 *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x98)%Z (mword_of_int 0x00006517 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x98) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00006517. Qed.
  Lemma pmsi_9c : PMS 0x9c false (ITYPE (mword_of_int 2378 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).  (* addi a0,a0,-1718 # 80007158 <etext+0x158> *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0x9c)%Z (mword_of_int 0x94a50513 : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0x9c) : mword 64) (ITYPE (mword_of_int 2378 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) pmsdec_9c. Qed.
  Lemma pmsi_a0 : PMS 0xa0 false (JAL (mword_of_int 2093072 : mword 21, Regidx (mword_of_int 1))).  (* jal 80000826 <panic> *)
  Proof. mk_base (KernelSyms.proc_mapstacks + 0xa0)%Z (mword_of_int 0x810ff0ef : mword 32) (mword_of_int (KernelSyms.proc_mapstacks + 0xa0) : mword 64) (JAL (mword_of_int 2093072 : mword 21, Regidx (mword_of_int 1))) bdec_810ff0ef. Qed.

End ProcMapstacksInstrs.
