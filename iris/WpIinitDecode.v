(* WpIinitDecode.v -- the instruction-DECODE layer for xv6's iinit().
   For every instruction of

     iinit @ 0x80003006 .. 0x8000305c   (offsets 0x00 .. 0x56)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([iii_<off>]) plus
   the per-instruction decode facts they consume ([iidc_<word>] compressed /
   [iidb_<word>] base).  Pure mirror of WpFreerangeDecode.v; iinit shares
   freerange's 48-byte / 6-slot frame, so the sixteen compressed words here are
   the same shared prologue/epilogue encodings (kept local, like every other
   function's decode file, so no decode file depends on another's). *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpDecodeBridge.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts (one per distinct 16-bit encoding).            *)
(* ===================================================================== *)

(* 0x7179  c.addi16sp sp,-48 *)
Lemma iidc_7179 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7179 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 61 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf406  c.sdsp ra,40(sp) *)
Lemma iidc_f406 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf406 : mword 16)) s
  = Some (C_SDSP (mword_of_int 5, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf022  c.sdsp s0,32(sp) *)
Lemma iidc_f022 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf022 : mword 16)) s
  = Some (C_SDSP (mword_of_int 4, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xec26  c.sdsp s1,24(sp) *)
Lemma iidc_ec26 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xec26 : mword 16)) s
  = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe84a  c.sdsp s2,16(sp) *)
Lemma iidc_e84a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe84a : mword 16)) s
  = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe44e  c.sdsp s3,8(sp) *)
Lemma iidc_e44e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe44e : mword 16)) s
  = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x1800  c.addi4spn s0,sp,48 *)
Lemma iidc_1800 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1800 : mword 16)) s
  = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 12 : mword 8), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x85ca  c.mv a1,s2 *)
Lemma iidc_85ca s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x85ca : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8526  c.mv a0,s1 *)
Lemma iidc_8526 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8526 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x70a2  c.ldsp ra,40(sp) *)
Lemma iidc_70a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x70a2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 5, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7402  c.ldsp s0,32(sp) *)
Lemma iidc_7402 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7402 : mword 16)) s
  = Some (C_LDSP (mword_of_int 4, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x64e2  c.ldsp s1,24(sp) *)
Lemma iidc_64e2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x64e2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6942  c.ldsp s2,16(sp) *)
Lemma iidc_6942 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6942 : mword 16)) s
  = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x69a2  c.ldsp s3,8(sp) *)
Lemma iidc_69a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x69a2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6145  c.addi16sp sp,48 *)
Lemma iidc_6145 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6145 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 3 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8082  c.jr ra *)
Lemma iidc_8082 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8082 : mword 16)) s
  = Some (C_JR (Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (32-bit) decode facts.                                           *)
(* ===================================================================== *)

(* auipc a1,0x4 / addi a1,a1,1036 -- a1 := &"itable" *)
Lemma iidb_00004597 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00004597 : mword 32)) s
  = Some (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma iidb_40c58593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40c58593 : mword 32)) s
  = Some (ITYPE (mword_of_int 1036 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* auipc a0,0x1e / addi a0,a0,-1964 -- a0 := &itable (the immediate is the
   decoder's POSITIVE RESIDUE 4096-1964 = 2132) *)
Lemma iidb_0001e517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e517 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma iidb_85450513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x85450513 : mword 32)) s
  = Some (ITYPE (mword_of_int 2132 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,initlock (backwards) *)
Lemma iidb_b65fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb65fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087780 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* auipc s1,0x1e / addi s1,s1,-1936 -- s1 := &itable.inode[0].lock *)
Lemma iidb_0001e497 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e497 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma iidb_87048493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x87048493 : mword 32)) s
  = Some (ITYPE (mword_of_int 2160 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* auipc s3,0x1f / addi s3,s3,760 -- s3 := the loop's end pointer *)
Lemma iidb_0001f997 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001f997 : mword 32)) s
  = Some (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 19), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma iidb_2f898993 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2f898993 : mword 32)) s
  = Some (ITYPE (mword_of_int 760 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* auipc s2,0x4 / addi s2,s2,1008 -- s2 := &"inode" *)
Lemma iidb_00004917 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00004917 : mword 32)) s
  = Some (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 18), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma iidb_3f090913 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x3f090913 : mword 32)) s
  = Some (ITYPE (mword_of_int 1008 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,initsleeplock (forwards) *)
Lemma iidb_653000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x653000ef : mword 32)) s
  = Some (JAL (mword_of_int 3666 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* addi s1,s1,136 -- the loop's cursor bump by sizeof(struct inode) *)
Lemma iidb_08848493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x08848493 : mword 32)) s
  = Some (ITYPE (mword_of_int 136 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* bne s1,s3,<loop top> -- the back edge (imm is the positive residue of -12) *)
Lemma iidb_ff349ae3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xff349ae3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8180 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 9), BNE), s).
Proof. decode_bridge_ms. Qed.

Section WpIinitDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation II := KernelSyms.iinit.

  (* ---- prologue: 6-slot frame, save ra/s0/s1/s2/s3, s0 := frame top ---- *)
  Lemma iii_00 : kernel_text -∗ instr (mword_of_int (II + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (II + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (II + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) iidc_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma iii_02 : kernel_text -∗ instr (mword_of_int (II + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (II + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (II + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) iidc_f406 exec_execute_C_SDSP. Qed.

  Lemma iii_04 : kernel_text -∗ instr (mword_of_int (II + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (II + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (II + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) iidc_f022 exec_execute_C_SDSP. Qed.

  Lemma iii_06 : kernel_text -∗ instr (mword_of_int (II + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (II + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (II + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) iidc_ec26 exec_execute_C_SDSP. Qed.

  Lemma iii_08 : kernel_text -∗ instr (mword_of_int (II + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (II + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (II + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) iidc_e84a exec_execute_C_SDSP. Qed.

  Lemma iii_0a : kernel_text -∗ instr (mword_of_int (II + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (II + 0x0a)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (II + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) iidc_e44e exec_execute_C_SDSP. Qed.

  Lemma iii_0c : kernel_text -∗ instr (mword_of_int (II + 0x0c) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (II + 0x0c)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (II + 0x0c) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) iidc_1800 exec_execute_C_ADDI4SPN. Qed.

  (* ---- a1 := &"itable", a0 := &itable, jal initlock ---- *)
  Lemma iii_0e : kernel_text -∗ instr (mword_of_int (II + 0x0e) : mword 64) false (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (II + 0x0e)%Z (mword_of_int 0x00004597 : mword 32)
    (mword_of_int (II + 0x0e) : mword 64) (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 11), AUIPC)) iidb_00004597. Qed.

  Lemma iii_12 : kernel_text -∗ instr (mword_of_int (II + 0x12) : mword 64) false (ITYPE (mword_of_int 1036 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (II + 0x12)%Z (mword_of_int 0x40c58593 : mword 32)
    (mword_of_int (II + 0x12) : mword 64) (ITYPE (mword_of_int 1036 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) iidb_40c58593. Qed.

  Lemma iii_16 : kernel_text -∗ instr (mword_of_int (II + 0x16) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (II + 0x16)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (II + 0x16) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) iidb_0001e517. Qed.

  Lemma iii_1a : kernel_text -∗ instr (mword_of_int (II + 0x1a) : mword 64) false (ITYPE (mword_of_int 2132 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (II + 0x1a)%Z (mword_of_int 0x85450513 : mword 32)
    (mword_of_int (II + 0x1a) : mword 64) (ITYPE (mword_of_int 2132 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) iidb_85450513. Qed.

  Lemma iii_1e : kernel_text -∗ instr (mword_of_int (II + 0x1e) : mword 64) false (JAL (mword_of_int 2087780 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (II + 0x1e)%Z (mword_of_int 0xb65fd0ef : mword 32)
    (mword_of_int (II + 0x1e) : mword 64) (JAL (mword_of_int 2087780 : mword 21, Regidx (mword_of_int 1))) iidb_b65fd0ef. Qed.

  (* ---- loop setup: s1 := &inode[0].lock, s3 := end, s2 := &"inode" ---- *)
  Lemma iii_22 : kernel_text -∗ instr (mword_of_int (II + 0x22) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (II + 0x22)%Z (mword_of_int 0x0001e497 : mword 32)
    (mword_of_int (II + 0x22) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)) iidb_0001e497. Qed.

  Lemma iii_26 : kernel_text -∗ instr (mword_of_int (II + 0x26) : mword 64) false (ITYPE (mword_of_int 2160 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (II + 0x26)%Z (mword_of_int 0x87048493 : mword 32)
    (mword_of_int (II + 0x26) : mword 64) (ITYPE (mword_of_int 2160 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) iidb_87048493. Qed.

  Lemma iii_2a : kernel_text -∗ instr (mword_of_int (II + 0x2a) : mword 64) false (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 19), AUIPC)).
  Proof. mk_base (II + 0x2a)%Z (mword_of_int 0x0001f997 : mword 32)
    (mword_of_int (II + 0x2a) : mword 64) (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 19), AUIPC)) iidb_0001f997. Qed.

  Lemma iii_2e : kernel_text -∗ instr (mword_of_int (II + 0x2e) : mword 64) false (ITYPE (mword_of_int 760 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI)).
  Proof. mk_base (II + 0x2e)%Z (mword_of_int 0x2f898993 : mword 32)
    (mword_of_int (II + 0x2e) : mword 64) (ITYPE (mword_of_int 760 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI)) iidb_2f898993. Qed.

  Lemma iii_32 : kernel_text -∗ instr (mword_of_int (II + 0x32) : mword 64) false (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 18), AUIPC)).
  Proof. mk_base (II + 0x32)%Z (mword_of_int 0x00004917 : mword 32)
    (mword_of_int (II + 0x32) : mword 64) (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 18), AUIPC)) iidb_00004917. Qed.

  Lemma iii_36 : kernel_text -∗ instr (mword_of_int (II + 0x36) : mword 64) false (ITYPE (mword_of_int 1008 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (II + 0x36)%Z (mword_of_int 0x3f090913 : mword 32)
    (mword_of_int (II + 0x36) : mword 64) (ITYPE (mword_of_int 1008 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) iidb_3f090913. Qed.

  (* ---- the loop body: a1 := s2, a0 := s1, jal initsleeplock, bump, test ---- *)
  Lemma iii_3a : kernel_text -∗ instr (mword_of_int (II + 0x3a) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (II + 0x3a)%Z (mword_of_int 0x85ca : mword 16)
    (mword_of_int (II + 0x3a) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)) iidc_85ca exec_execute_C_MV. Qed.

  Lemma iii_3c : kernel_text -∗ instr (mword_of_int (II + 0x3c) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (II + 0x3c)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (II + 0x3c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) iidc_8526 exec_execute_C_MV. Qed.

  Lemma iii_3e : kernel_text -∗ instr (mword_of_int (II + 0x3e) : mword 64) false (JAL (mword_of_int 3666 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (II + 0x3e)%Z (mword_of_int 0x653000ef : mword 32)
    (mword_of_int (II + 0x3e) : mword 64) (JAL (mword_of_int 3666 : mword 21, Regidx (mword_of_int 1))) iidb_653000ef. Qed.

  Lemma iii_42 : kernel_text -∗ instr (mword_of_int (II + 0x42) : mword 64) false (ITYPE (mword_of_int 136 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (II + 0x42)%Z (mword_of_int 0x08848493 : mword 32)
    (mword_of_int (II + 0x42) : mword 64) (ITYPE (mword_of_int 136 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) iidb_08848493. Qed.

  Lemma iii_46 : kernel_text -∗ instr (mword_of_int (II + 0x46) : mword 64) false (BTYPE (mword_of_int 8180 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 9), BNE)).
  Proof. mk_base (II + 0x46)%Z (mword_of_int 0xff349ae3 : mword 32)
    (mword_of_int (II + 0x46) : mword 64) (BTYPE (mword_of_int 8180 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 9), BNE)) iidb_ff349ae3. Qed.

  (* ---- epilogue: restore ra/s0/s1/s2/s3, frame trade back, ret ---- *)
  Lemma iii_4a : kernel_text -∗ instr (mword_of_int (II + 0x4a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (II + 0x4a)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (II + 0x4a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) iidc_70a2 exec_execute_C_LDSP. Qed.

  Lemma iii_4c : kernel_text -∗ instr (mword_of_int (II + 0x4c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (II + 0x4c)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (II + 0x4c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) iidc_7402 exec_execute_C_LDSP. Qed.

  Lemma iii_4e : kernel_text -∗ instr (mword_of_int (II + 0x4e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (II + 0x4e)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (II + 0x4e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) iidc_64e2 exec_execute_C_LDSP. Qed.

  Lemma iii_50 : kernel_text -∗ instr (mword_of_int (II + 0x50) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (II + 0x50)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (II + 0x50) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) iidc_6942 exec_execute_C_LDSP. Qed.

  Lemma iii_52 : kernel_text -∗ instr (mword_of_int (II + 0x52) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (II + 0x52)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (II + 0x52) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) iidc_69a2 exec_execute_C_LDSP. Qed.

  Lemma iii_54 : kernel_text -∗ instr (mword_of_int (II + 0x54) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (II + 0x54)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (II + 0x54) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) iidc_6145 exec_execute_C_ADDI16SP. Qed.

  Lemma iii_56 : kernel_text -∗ instr (mword_of_int (II + 0x56) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (II + 0x56)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (II + 0x56) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) iidc_8082 exec_execute_C_JR. Qed.

End WpIinitDecode.
