(* CodeBinit.v -- the instruction-DECODE layer for xv6's binit().
   For every instruction of

     binit @ 0x80002ab0 .. 0x80002b34   (offsets 0x00 .. 0x84)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([bii_<off>]) plus
   the per-instruction decode facts they consume ([bidc_<word>] compressed /
   [bidb_<word>] base).  Pure mirror of CodeFreerange.v; binit shares
   freerange's 48-byte / 6-slot frame, so every frame word comes from the shared
   [cdec_*] templates in KernelRvcDecode.v and only binit's own words are
   proved here.

   The two compressed [c.sd]s (the buffer's next field and the old head-next's
   prev field) are the only instructions whose AST needs massaging: the RVC
   expansion yields a STORE over [creg2reg_idx] register indices and a
   [zero_extend'] of the scaled 5-bit offset, while the [wp_csd_s_sconf] leaf
   wants plain [Regidx]es and a 12-bit immediate.  Both forms are convertible,
   so the bridge is three [vm_compute] equations rewritten into the goal before
   [mk_rvc] runs -- done HERE so binit's proof only ever sees the leaf's
   shape. *)
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
Require Import KernelRvcDecode KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts (one per distinct 16-bit encoding).            *)
(* ===================================================================== *)

(* 0x89ba  c.mv s3,a4 *)
Lemma bidc_89ba s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x89ba : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 19), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe8bc  c.sd a5,80(s1) *)
Lemma bidc_e8bc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe8bc : mword 16)) s
  = Some (C_SD (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* [cdec_85d2] -- shared, see KernelRvcDecode.v *)

(* 0xe7a4  c.sd s1,72(a5) *)
Lemma bidc_e7a4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe7a4 : mword 16)) s
  = Some (C_SD (mword_of_int 9, Cregidx (mword_of_int 7), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (32-bit) decode facts.  The negative addi immediates appear as the *)
(* decoder's POSITIVE RESIDUE (-1840 -> 2256, and so on).                  *)
(* ===================================================================== *)

Lemma bidb_8d058593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8d058593 : mword 32)) s
  = Some (ITYPE (mword_of_int 2256 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* a0 := &bcache: the auipc half is the shared [bdec_00015517] (sys_uptime
   materializes &tickslock with the same word); the addi is binit's own. *)
Lemma bidb_6c850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6c850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1736 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bidb_6bc78793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6bc78793 : mword 32)) s
  = Some (ITYPE (mword_of_int 1724 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bidb_91c70713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x91c70713 : mword 32)) s
  = Some (ITYPE (mword_of_int 2332 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* sd a4,688(a5) / sd a4,696(a5) -- head.prev := &head; head.next := &head *)
Lemma bidb_2ae7b823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2ae7b823 : mword 32)) s
  = Some (STORE (mword_of_int 688 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 8), s).
Proof. decode_bridge_ms. Qed.

Lemma bidb_2ae7bc23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2ae7bc23 : mword 32)) s
  = Some (STORE (mword_of_int 696 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 8), s).
Proof. decode_bridge_ms. Qed.

(* auipc s1,0x15 / addi s1,s1,1724 -- s1 := &bcache.buf[0] *)
Lemma bidb_00015497 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00015497 : mword 32)) s
  = Some (UTYPE (mword_of_int 21 : mword 20, Regidx (mword_of_int 9), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma bidb_6bc48493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6bc48493 : mword 32)) s
  = Some (ITYPE (mword_of_int 1724 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* auipc s4,0x5 / addi s4,s4,-1888 -- s4 := &"buffer" *)
Lemma bidb_00005a17 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00005a17 : mword 32)) s
  = Some (UTYPE (mword_of_int 5 : mword 20, Regidx (mword_of_int 20), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma bidb_8a0a0a13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8a0a0a13 : mword 32)) s
  = Some (ITYPE (mword_of_int 2208 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* ld a5,696(s2) -- a5 := bcache.head.next (twice per iteration) *)
Lemma bidb_2b893783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2b893783 : mword 32)) s
  = Some (LOAD (mword_of_int 696 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* sd s3,72(s1) -- b->prev := &bcache.head *)
Lemma bidb_0534b423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0534b423 : mword 32)) s
  = Some (STORE (mword_of_int 72 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 9), 8), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,initsleeplock (forwards) *)
Lemma bidb_386010ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x386010ef : mword 32)) s
  = Some (JAL (mword_of_int 4998 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* sd s1,696(s2) -- bcache.head.next := b *)
Lemma bidb_2a993c23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2a993c23 : mword 32)) s
  = Some (STORE (mword_of_int 696 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 18), 8), s).
Proof. decode_bridge_ms. Qed.

(* addi s1,s1,1112 -- the loop's cursor bump by sizeof(struct buf) *)
Lemma bidb_45848493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x45848493 : mword 32)) s
  = Some (ITYPE (mword_of_int 1112 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* bne s1,s3,<loop top> -- the back edge (imm is the positive residue of -34) *)
Lemma bidb_fd349fe3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd349fe3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8158 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 9), BNE), s).
Proof. decode_bridge_ms. Qed.

(* ---- the c.sd AST bridges (see the file header) ---- *)
Lemma bid_csd_imm80 :
  zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")) = (mword_of_int 80 : mword 12).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma bid_csd_imm72 :
  zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")) = (mword_of_int 72 : mword 12).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma bid_cr1 : creg2reg_idx (Cregidx (mword_of_int 1)) = Regidx (mword_of_int 9).
Proof. vm_compute. reflexivity. Qed.
Lemma bid_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx (mword_of_int 15).
Proof. vm_compute. reflexivity. Qed.

Section CodeBinit.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation BI := KernelSyms.binit.

  (* ---- prologue: 6-slot frame, save ra/s0/s1/s2/s3/s4, s0 := frame top ---- *)
  Lemma bii_00 : kernel_text -∗ instr (mword_of_int (BI + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (BI + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (BI + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma bii_02 : kernel_text -∗ instr (mword_of_int (BI + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (BI + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (BI + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  Lemma bii_04 : kernel_text -∗ instr (mword_of_int (BI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (BI + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (BI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  Lemma bii_06 : kernel_text -∗ instr (mword_of_int (BI + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (BI + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (BI + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  Lemma bii_08 : kernel_text -∗ instr (mword_of_int (BI + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (BI + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (BI + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  Lemma bii_0a : kernel_text -∗ instr (mword_of_int (BI + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (BI + 0x0a)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (BI + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_e44e exec_execute_C_SDSP. Qed.

  Lemma bii_0c : kernel_text -∗ instr (mword_of_int (BI + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (BI + 0x0c)%Z (mword_of_int 0xe052 : mword 16)
    (mword_of_int (BI + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_e052 exec_execute_C_SDSP. Qed.

  Lemma bii_0e : kernel_text -∗ instr (mword_of_int (BI + 0x0e) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (BI + 0x0e)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (BI + 0x0e) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  (* ---- a1 := &"bcache", a0 := &bcache, jal initlock ---- *)
  Lemma bii_10 : kernel_text -∗ instr (mword_of_int (BI + 0x10) : mword 64) false (UTYPE (mword_of_int 5 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (BI + 0x10)%Z (mword_of_int 0x00005597 : mword 32)
    (mword_of_int (BI + 0x10) : mword 64) (UTYPE (mword_of_int 5 : mword 20, Regidx (mword_of_int 11), AUIPC)) bdec_00005597. Qed.

  Lemma bii_14 : kernel_text -∗ instr (mword_of_int (BI + 0x14) : mword 64) false (ITYPE (mword_of_int 2256 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (BI + 0x14)%Z (mword_of_int 0x8d058593 : mword 32)
    (mword_of_int (BI + 0x14) : mword 64) (ITYPE (mword_of_int 2256 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) bidb_8d058593. Qed.

  Lemma bii_18 : kernel_text -∗ instr (mword_of_int (BI + 0x18) : mword 64) false (UTYPE (mword_of_int 21 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (BI + 0x18)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (BI + 0x18) : mword 64) (UTYPE (mword_of_int 21 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma bii_1c : kernel_text -∗ instr (mword_of_int (BI + 0x1c) : mword 64) false (ITYPE (mword_of_int 1736 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BI + 0x1c)%Z (mword_of_int 0x6c850513 : mword 32)
    (mword_of_int (BI + 0x1c) : mword 64) (ITYPE (mword_of_int 1736 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) bidb_6c850513. Qed.

  Lemma bii_20 : kernel_text -∗ instr (mword_of_int (BI + 0x20) : mword 64) false (JAL (mword_of_int 2089144 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BI + 0x20)%Z (mword_of_int 0x8b8fe0ef : mword 32)
    (mword_of_int (BI + 0x20) : mword 64) (JAL (mword_of_int 2089144 : mword 21, Regidx (mword_of_int 1))) bdec_8b8fe0ef. Qed.

  (* ---- the head sentinel: a5 := head-field base, a4 := &head, both links ---- *)
  Lemma bii_24 : kernel_text -∗ instr (mword_of_int (BI + 0x24) : mword 64) false (UTYPE (mword_of_int 29 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (BI + 0x24)%Z (mword_of_int 0x0001d797 : mword 32)
    (mword_of_int (BI + 0x24) : mword 64) (UTYPE (mword_of_int 29 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0001d797. Qed.

  Lemma bii_28 : kernel_text -∗ instr (mword_of_int (BI + 0x28) : mword 64) false (ITYPE (mword_of_int 1724 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (BI + 0x28)%Z (mword_of_int 0x6bc78793 : mword 32)
    (mword_of_int (BI + 0x28) : mword 64) (ITYPE (mword_of_int 1724 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) bidb_6bc78793. Qed.

  Lemma bii_2c : kernel_text -∗ instr (mword_of_int (BI + 0x2c) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (BI + 0x2c)%Z (mword_of_int 0x0001e717 : mword 32)
    (mword_of_int (BI + 0x2c) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)) bdec_0001e717. Qed.

  Lemma bii_30 : kernel_text -∗ instr (mword_of_int (BI + 0x30) : mword 64) false (ITYPE (mword_of_int 2332 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (BI + 0x30)%Z (mword_of_int 0x91c70713 : mword 32)
    (mword_of_int (BI + 0x30) : mword 64) (ITYPE (mword_of_int 2332 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) bidb_91c70713. Qed.

  Lemma bii_34 : kernel_text -∗ instr (mword_of_int (BI + 0x34) : mword 64) false (STORE (mword_of_int 688 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 8)).
  Proof. mk_base (BI + 0x34)%Z (mword_of_int 0x2ae7b823 : mword 32)
    (mword_of_int (BI + 0x34) : mword 64) (STORE (mword_of_int 688 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 8)) bidb_2ae7b823. Qed.

  Lemma bii_38 : kernel_text -∗ instr (mword_of_int (BI + 0x38) : mword 64) false (STORE (mword_of_int 696 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 8)).
  Proof. mk_base (BI + 0x38)%Z (mword_of_int 0x2ae7bc23 : mword 32)
    (mword_of_int (BI + 0x38) : mword 64) (STORE (mword_of_int 696 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 8)) bidb_2ae7bc23. Qed.

  (* ---- loop setup: s1 := &buf[0], s2 := a5, s3 := a4, s4 := &"buffer" ---- *)
  Lemma bii_3c : kernel_text -∗ instr (mword_of_int (BI + 0x3c) : mword 64) false (UTYPE (mword_of_int 21 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (BI + 0x3c)%Z (mword_of_int 0x00015497 : mword 32)
    (mword_of_int (BI + 0x3c) : mword 64) (UTYPE (mword_of_int 21 : mword 20, Regidx (mword_of_int 9), AUIPC)) bidb_00015497. Qed.

  Lemma bii_40 : kernel_text -∗ instr (mword_of_int (BI + 0x40) : mword 64) false (ITYPE (mword_of_int 1724 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (BI + 0x40)%Z (mword_of_int 0x6bc48493 : mword 32)
    (mword_of_int (BI + 0x40) : mword 64) (ITYPE (mword_of_int 1724 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) bidb_6bc48493. Qed.

  Lemma bii_44 : kernel_text -∗ instr (mword_of_int (BI + 0x44) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (BI + 0x44)%Z (mword_of_int 0x893e : mword 16)
    (mword_of_int (BI + 0x44) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 18), ADD)) cdec_893e exec_execute_C_MV. Qed.

  Lemma bii_46 : kernel_text -∗ instr (mword_of_int (BI + 0x46) : mword 64) true (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (BI + 0x46)%Z (mword_of_int 0x89ba : mword 16)
    (mword_of_int (BI + 0x46) : mword 64) (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 19), ADD)) bidc_89ba exec_execute_C_MV. Qed.

  Lemma bii_48 : kernel_text -∗ instr (mword_of_int (BI + 0x48) : mword 64) false (UTYPE (mword_of_int 5 : mword 20, Regidx (mword_of_int 20), AUIPC)).
  Proof. mk_base (BI + 0x48)%Z (mword_of_int 0x00005a17 : mword 32)
    (mword_of_int (BI + 0x48) : mword 64) (UTYPE (mword_of_int 5 : mword 20, Regidx (mword_of_int 20), AUIPC)) bidb_00005a17. Qed.

  Lemma bii_4c : kernel_text -∗ instr (mword_of_int (BI + 0x4c) : mword 64) false (ITYPE (mword_of_int 2208 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)).
  Proof. mk_base (BI + 0x4c)%Z (mword_of_int 0x8a0a0a13 : mword 32)
    (mword_of_int (BI + 0x4c) : mword 64) (ITYPE (mword_of_int 2208 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)) bidb_8a0a0a13. Qed.

  (* ---- the loop body ---- *)
  Lemma bii_50 : kernel_text -∗ instr (mword_of_int (BI + 0x50) : mword 64) false (LOAD (mword_of_int 696 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (BI + 0x50)%Z (mword_of_int 0x2b893783 : mword 32)
    (mword_of_int (BI + 0x50) : mword 64) (LOAD (mword_of_int 696 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), false, 8)) bidb_2b893783. Qed.

  (* c.sd a5,80(s1) : b->next := the loaded head.next -- stated in the leaf's
     shape via the three bridges above. *)
  Lemma bii_54 : kernel_text -∗ instr (mword_of_int (BI + 0x54) : mword 64) true (STORE (mword_of_int 80 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 8)).
  Proof.
    rewrite -bid_csd_imm80 -bid_cr1 -bid_cr7.
    mk_rvc (BI + 0x54)%Z (mword_of_int 0xe8bc : mword 16)
      (mword_of_int (BI + 0x54) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 1)), 8)) bidc_e8bc exec_execute_C_SD.
  Qed.

  Lemma bii_56 : kernel_text -∗ instr (mword_of_int (BI + 0x56) : mword 64) false (STORE (mword_of_int 72 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 9), 8)).
  Proof. mk_base (BI + 0x56)%Z (mword_of_int 0x0534b423 : mword 32)
    (mword_of_int (BI + 0x56) : mword 64) (STORE (mword_of_int 72 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 9), 8)) bidb_0534b423. Qed.

  Lemma bii_5a : kernel_text -∗ instr (mword_of_int (BI + 0x5a) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (BI + 0x5a)%Z (mword_of_int 0x85d2 : mword 16)
    (mword_of_int (BI + 0x5a) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 11), ADD)) cdec_85d2 exec_execute_C_MV. Qed.

  Lemma bii_5c : kernel_text -∗ instr (mword_of_int (BI + 0x5c) : mword 64) false (ITYPE (mword_of_int 16 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BI + 0x5c)%Z (mword_of_int 0x01048513 : mword 32)
    (mword_of_int (BI + 0x5c) : mword 64) (ITYPE (mword_of_int 16 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)) bdec_01048513. Qed.

  Lemma bii_60 : kernel_text -∗ instr (mword_of_int (BI + 0x60) : mword 64) false (JAL (mword_of_int 4998 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BI + 0x60)%Z (mword_of_int 0x386010ef : mword 32)
    (mword_of_int (BI + 0x60) : mword 64) (JAL (mword_of_int 4998 : mword 21, Regidx (mword_of_int 1))) bidb_386010ef. Qed.

  Lemma bii_64 : kernel_text -∗ instr (mword_of_int (BI + 0x64) : mword 64) false (LOAD (mword_of_int 696 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (BI + 0x64)%Z (mword_of_int 0x2b893783 : mword 32)
    (mword_of_int (BI + 0x64) : mword 64) (LOAD (mword_of_int 696 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), false, 8)) bidb_2b893783. Qed.

  (* c.sd s1,72(a5) : (head.next)->prev := b *)
  Lemma bii_68 : kernel_text -∗ instr (mword_of_int (BI + 0x68) : mword 64) true (STORE (mword_of_int 72 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), 8)).
  Proof.
    rewrite -bid_csd_imm72 -bid_cr7 -bid_cr1.
    mk_rvc (BI + 0x68)%Z (mword_of_int 0xe7a4 : mword 16)
      (mword_of_int (BI + 0x68) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), 8)) bidc_e7a4 exec_execute_C_SD.
  Qed.

  Lemma bii_6a : kernel_text -∗ instr (mword_of_int (BI + 0x6a) : mword 64) false (STORE (mword_of_int 696 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 18), 8)).
  Proof. mk_base (BI + 0x6a)%Z (mword_of_int 0x2a993c23 : mword 32)
    (mword_of_int (BI + 0x6a) : mword 64) (STORE (mword_of_int 696 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 18), 8)) bidb_2a993c23. Qed.

  Lemma bii_6e : kernel_text -∗ instr (mword_of_int (BI + 0x6e) : mword 64) false (ITYPE (mword_of_int 1112 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (BI + 0x6e)%Z (mword_of_int 0x45848493 : mword 32)
    (mword_of_int (BI + 0x6e) : mword 64) (ITYPE (mword_of_int 1112 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) bidb_45848493. Qed.

  Lemma bii_72 : kernel_text -∗ instr (mword_of_int (BI + 0x72) : mword 64) false (BTYPE (mword_of_int 8158 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 9), BNE)).
  Proof. mk_base (BI + 0x72)%Z (mword_of_int 0xfd349fe3 : mword 32)
    (mword_of_int (BI + 0x72) : mword 64) (BTYPE (mword_of_int 8158 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 9), BNE)) bidb_fd349fe3. Qed.

  (* ---- epilogue ---- *)
  Lemma bii_76 : kernel_text -∗ instr (mword_of_int (BI + 0x76) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (BI + 0x76)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (BI + 0x76) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  Lemma bii_78 : kernel_text -∗ instr (mword_of_int (BI + 0x78) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (BI + 0x78)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (BI + 0x78) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  Lemma bii_7a : kernel_text -∗ instr (mword_of_int (BI + 0x7a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (BI + 0x7a)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (BI + 0x7a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma bii_7c : kernel_text -∗ instr (mword_of_int (BI + 0x7c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (BI + 0x7c)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (BI + 0x7c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  Lemma bii_7e : kernel_text -∗ instr (mword_of_int (BI + 0x7e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (BI + 0x7e)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (BI + 0x7e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69a2 exec_execute_C_LDSP. Qed.

  Lemma bii_80 : kernel_text -∗ instr (mword_of_int (BI + 0x80) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (BI + 0x80)%Z (mword_of_int 0x6a02 : mword 16)
    (mword_of_int (BI + 0x80) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_6a02 exec_execute_C_LDSP. Qed.

  Lemma bii_82 : kernel_text -∗ instr (mword_of_int (BI + 0x82) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (BI + 0x82)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (BI + 0x82) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  Lemma bii_84 : kernel_text -∗ instr (mword_of_int (BI + 0x84) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (BI + 0x84)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (BI + 0x84) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeBinit.
