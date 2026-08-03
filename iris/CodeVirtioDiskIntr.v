(* CodeVirtioDiskIntr.v -- the instruction-DECODE layer for xv6's
   virtio_disk_intr().

   For every instruction of

     virtio_disk_intr @ 0x80005962 .. 0x80005a0e   (offsets 0x00 .. 0xac)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([vti_<off>]).

   The 32-byte frame prologue/epilogue (c.addi sp,-32 / c.sdsp ra,24 /
   c.sdsp s0,16 / c.sdsp s1,8 / c.addi4spn s0,sp,32 ... c.ldsp ra,24 /
   c.ldsp s0,16 / c.ldsp s1,8 / c.addi16sp sp,32 / c.ret) is the standard
   4-slot shape, so those decodes reuse KernelRvcDecode.v's shared bit-keyed
   [cdec_<word>] templates; so do [c.add a5,a5,a4], [c.slli a5,3] and
   [c.addiw a5,1].  Everything else is virtio_disk_intr's own.

     0x00 1101        c.addi   sp,-32
     0x02 ec06        c.sdsp   ra,24(sp)
     0x04 e822        c.sdsp   s0,16(sp)
     0x06 e426        c.sdsp   s1,8(sp)
     0x08 1000        c.addi4spn s0,sp,32
     0x0a 0001e497    auipc    s1,0x1e
     0x0e aac48493    addi     s1,s1,-1364        # s1 = &disk
     0x12 0001e517    auipc    a0,0x1e
     0x16 bcc50513    addi     a0,a0,-1076        # a0 = &disk.vdisk_lock
     0x1a a8cfb0ef    jal      acquire
     0x1e 100017b7    lui      a5,0x10001
     0x22 53bc        c.lw     a5,96(a5)          # *R(INTERRUPT_STATUS)
     0x24 8b8d        c.andi   a5,3
     0x26 10001737    lui      a4,0x10001
     0x2a d37c        c.sw     a5,100(a4)         # *R(INTERRUPT_ACK) = .. & 3
     0x2c 0330000f    fence    rw,rw
     0x30 689c        c.ld     a5,16(s1)          # disk.used
     0x32 0204d703    lhu      a4,32(s1)          # disk.used_idx
     0x36 0027d783    lhu      a5,2(a5)           # disk.used->idx
     0x3a 04f70863    beq      a4,a5,+0x50        # -> 0x8a  loop EXIT
     ---- loop head (back edge target) ----
     0x3e 0330000f    fence    rw,rw
     0x42 6898        c.ld     a4,16(s1)          # disk.used
     0x44 0204d783    lhu      a5,32(s1)          # disk.used_idx
     0x48 8b9d        c.andi   a5,7               # % NUM
     0x4a 078e        c.slli   a5,3               # * 8  (sizeof used elem)
     0x4c 97ba        c.add    a5,a5,a4
     0x4e 43dc        c.lw     a5,4(a5)           # id = used->ring[..].id
     0x50 00479713    slli     a4,a5,0x4
     0x54 02070713    addi     a4,a4,32
     0x58 9726        c.add    a4,a4,s1           # &disk.info[id]
     0x5a 01074703    lbu      a4,16(a4)          # disk.info[id].status
     0x5e e329        c.bnez   a4,+0x42           # -> 0xa0  panic (REFUTED)
     0x60 0792        c.slli   a5,4
     0x62 02078793    addi     a5,a5,32
     0x66 97a6        c.add    a5,a5,s1
     0x68 6788        c.ld     a0,8(a5)           # b = disk.info[id].b
     0x6a 00052223    sw       zero,4(a0)         # b->disk = 0
     0x6e d82fc0ef    jal      wakeup
     0x72 0204d783    lhu      a5,32(s1)
     0x76 2785        c.addiw  a5,1
     0x78 17c2        c.slli   a5,0x30
     0x7a 93c1        c.srli   a5,0x30            # 16-bit wrap
     0x7c 02f49023    sh       a5,32(s1)          # disk.used_idx += 1
     0x80 6898        c.ld     a4,16(s1)
     0x82 00275703    lhu      a4,2(a4)           # disk.used->idx
     0x86 faf71ce3    bne      a4,a5,-0x48        # -> 0x3e  loop BACK EDGE
     ---- exit ----
     0x8a 0001e517    auipc    a0,0x1e
     0x8e b5450513    addi     a0,a0,-1196        # a0 = &disk.vdisk_lock
     0x92 a9cfb0ef    jal      release
     0x96 60e2        c.ldsp   ra,24(sp)
     0x98 6442        c.ldsp   s0,16(sp)
     0x9a 64a2        c.ldsp   s1,8(sp)
     0x9c 6105        c.addi16sp sp,32
     0x9e 8082        c.ret
     0xa0 00002517    auipc    a0,0x2             # panic("virtio_disk_intr status")
     0xa4 cf650513    addi     a0,a0,-778
     0xa8 e1dfa0ef    jal      panic

   The panic tail at +0xa0..+0xac is DEAD: the protocol pins a completed
   slot's status byte at 0 (VirtioProto.virtio_proto_reclaim_acc's payoff),
   so the [c.bnez] at +0x5e provably falls through and no [instr] fact is
   needed for those three instructions.                                    *)
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
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Notation VDT := KernelSyms.virtio_disk_intr.

(* ===================================================================== *)
(* Compressed words virtio_disk_intr does not share with another function. *)
(* ===================================================================== *)

(* +0x22  c.lw a5,96(a5) -- *R(VIRTIO_MMIO_INTERRUPT_STATUS) *)
Lemma vtc_53bc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x53bc : mword 16)) s
  = Some (C_LW (mword_of_int 24, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vte_53bc s :
  exec (execute (C_LW (mword_of_int 24, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 96, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* +0x24  c.andi a5,3 *)
Lemma vtc_8b8d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8b8d : mword 16)) s
  = Some (C_ANDI (mword_of_int 3, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vte_8b8d s :
  exec (execute (C_ANDI (mword_of_int 3, Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)), s).
Proof. apply exec_execute_C_ANDI_leaf. vm_compute. reflexivity. Qed.

(* +0x2a  c.sw a5,100(a4) -- *R(VIRTIO_MMIO_INTERRUPT_ACK) *)
Lemma vtc_d37c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd37c : mword 16)) s
  = Some (C_SW (mword_of_int 25, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vte_d37c s :
  exec (execute (C_SW (mword_of_int 25, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 100, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.


Lemma vte_689c s :
  exec (execute (C_LD (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* +0x42 / +0x80  c.ld a4,16(s1) -- disk.used *)
Lemma vtc_6898 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6898 : mword 16)) s
  = Some (C_LD (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vte_6898 s :
  exec (execute (C_LD (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* +0x48  c.andi a5,7 -- disk.used_idx % NUM *)
Lemma vtc_8b9d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8b9d : mword 16)) s
  = Some (C_ANDI (mword_of_int 7, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vte_8b9d s :
  exec (execute (C_ANDI (mword_of_int 7, Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 (mword_of_int 7 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)), s).
Proof. apply exec_execute_C_ANDI_leaf. vm_compute. reflexivity. Qed.


Lemma vte_43dc s :
  exec (execute (C_LW (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.


(* +0x5e  c.bnez a4,+0x42  (0x42 = 66 = 2 * 33) -- the status panic *)
Lemma vtc_e329 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe329 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 33, Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x60  c.slli a5,4 *)
Lemma vtc_0792 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0792 : mword 16)) s
  = Some (C_SLLI (mword_of_int 4, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* +0x68  c.ld a0,8(a5) -- b = disk.info[id].b *)
Lemma vtc_6788 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6788 : mword 16)) s
  = Some (C_LD (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vte_6788 s :
  exec (execute (C_LD (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 8, Regidx (mword_of_int 15), Regidx (mword_of_int 10), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* +0x78  c.slli a5,0x30 *)
Lemma vtc_17c2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x17c2 : mword 16)) s
  = Some (C_SLLI (mword_of_int 48, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x7a  c.srli a5,0x30 *)
Lemma vtc_93c1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x93c1 : mword 16)) s
  = Some (C_SRLI (mword_of_int 48, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* [decode_bridge_ms] closes its result equation with a bare [vm_compute;
   reflexivity], which needs the decoded AST's literals to be CONVERTIBLE at
   the head -- true for every AST whose immediates are [mword 12]/[mword 13]/
   [mword 20]/[mword 21] literals.  FENCE's four-bit pred/succ fields are not
   (they arrive as a slice, and only [bv_eq] closes them), so that one word
   uses WpDecodeBridge's leafwise-[bv_eq] variant [decode_bridge_ms_bv]. *)

(* +0x0e  addi s1,s1,-1364  -- s1 = &disk *)
Lemma vtb_aac48493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xaac48493 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xaac : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x16  addi a0,a0,-1076 -- a0 = &disk.vdisk_lock *)
Lemma vtb_bcc50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xbcc50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xbcc : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x1a  jal ra,acquire  (0x8000597c -> 0x80000c08 is -19828; 2^21 - 19828) *)
Lemma vtb_a8cfb0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa8cfb0ef : mword 32)) s
  = Some (JAL (mword_of_int 2077324 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.



(* +0x32  lhu a4,32(s1) -- disk.used_idx *)
Lemma vtb_0204d703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0204d703 : mword 32)) s
  = Some (LOAD (mword_of_int 32 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), true, 2), s).
Proof. decode_bridge_ms. Qed.

(* +0x36  lhu a5,2(a5) -- disk.used->idx *)
Lemma vtb_0027d783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0027d783 : mword 32)) s
  = Some (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 2), s).
Proof. decode_bridge_ms. Qed.


(* +0x44 / +0x72  lhu a5,32(s1) -- disk.used_idx *)
Lemma vtb_0204d783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0204d783 : mword 32)) s
  = Some (LOAD (mword_of_int 32 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), true, 2), s).
Proof. decode_bridge_ms. Qed.

(* +0x50  slli a4,a5,0x4 *)
Lemma vtb_00479713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00479713 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 14), SLLI), s).
Proof. decode_bridge_ms. Qed.


(* +0x5a  lbu a4,16(a4) -- disk.info[id].status *)
Lemma vtb_01074703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01074703 : mword 32)) s
  = Some (LOAD (mword_of_int 16 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* +0x62  addi a5,a5,32 *)
Lemma vtb_02078793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02078793 : mword 32)) s
  = Some (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x6a  sw zero,4(a0) -- b->disk = 0 *)
Lemma vtb_00052223 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00052223 : mword 32)) s
  = Some (STORE (mword_of_int 4 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4), s).
Proof. decode_bridge_ms. Qed.

(* +0x6e  jal ra,wakeup  (0x800059d0 -> 0x80001f52 is -14974; 2^21 - 14974) *)
Lemma vtb_d82fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd82fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2082178 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x7c  sh a5,32(s1) -- disk.used_idx += 1 *)
Lemma vtb_02f49023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02f49023 : mword 32)) s
  = Some (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 2), s).
Proof. decode_bridge_ms. Qed.

(* +0x82  lhu a4,2(a4) -- disk.used->idx *)
Lemma vtb_00275703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00275703 : mword 32)) s
  = Some (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), true, 2), s).
Proof. decode_bridge_ms. Qed.

(* +0x86  bne a4,a5,-0x48 -- the loop BACK EDGE (2^13 - 72) *)
Lemma vtb_faf71ce3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfaf71ce3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8120 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE), s).
Proof. decode_bridge_ms. Qed.

(* +0x8e  addi a0,a0,-1196 -- a0 = &disk.vdisk_lock *)
Lemma vtb_b5450513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb5450513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xb54 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x92  jal ra,release  (0x800059f4 -> 0x80000c90 is -19812; 2^21 - 19812) *)
Lemma vtb_a9cfb0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa9cfb0ef : mword 32)) s
  = Some (JAL (mword_of_int 2077340 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section VirtioDiskIntrInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ---- prologue: 32-byte frame, saves ra/s0/s1 ---- *)
  Lemma vti_00 : kernel_text -∗ instr (mword_of_int (VDT + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (VDT + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (VDT + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma vti_02 : kernel_text -∗ instr (mword_of_int (VDT + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (VDT + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (VDT + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma vti_04 : kernel_text -∗ instr (mword_of_int (VDT + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (VDT + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (VDT + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma vti_06 : kernel_text -∗ instr (mword_of_int (VDT + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (VDT + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (VDT + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma vti_08 : kernel_text -∗ instr (mword_of_int (VDT + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (VDT + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (VDT + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* ---- s1 := &disk ; a0 := &disk.vdisk_lock ; acquire ---- *)
  Lemma vti_0a : kernel_text -∗ instr (mword_of_int (VDT + 0x0a) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (VDT + 0x0a)%Z (mword_of_int 0x0001e497 : mword 32)
    (mword_of_int (VDT + 0x0a) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)) bdec_0001e497. Qed.

  Lemma vti_0e : kernel_text -∗ instr (mword_of_int (VDT + 0x0e) : mword 64) false (ITYPE (mword_of_int 0xaac : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (VDT + 0x0e)%Z (mword_of_int 0xaac48493 : mword 32)
    (mword_of_int (VDT + 0x0e) : mword 64) (ITYPE (mword_of_int 0xaac : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) vtb_aac48493. Qed.

  Lemma vti_12 : kernel_text -∗ instr (mword_of_int (VDT + 0x12) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (VDT + 0x12)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (VDT + 0x12) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  Lemma vti_16 : kernel_text -∗ instr (mword_of_int (VDT + 0x16) : mword 64) false (ITYPE (mword_of_int 0xbcc : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (VDT + 0x16)%Z (mword_of_int 0xbcc50513 : mword 32)
    (mword_of_int (VDT + 0x16) : mword 64) (ITYPE (mword_of_int 0xbcc : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) vtb_bcc50513. Qed.

  Lemma vti_1a : kernel_text -∗ instr (mword_of_int (VDT + 0x1a) : mword 64) false (JAL (mword_of_int 2077324 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VDT + 0x1a)%Z (mword_of_int 0xa8cfb0ef : mword 32)
    (mword_of_int (VDT + 0x1a) : mword 64) (JAL (mword_of_int 2077324 : mword 21, Regidx (mword_of_int 1))) vtb_a8cfb0ef. Qed.

  (* ---- the ISR read/ack ---- *)
  Lemma vti_1e : kernel_text -∗ instr (mword_of_int (VDT + 0x1e) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (VDT + 0x1e)%Z (mword_of_int 0x100017b7 : mword 32)
    (mword_of_int (VDT + 0x1e) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)) bdec_100017b7. Qed.

  Lemma vti_22 : kernel_text -∗ instr (mword_of_int (VDT + 0x22) : mword 64) true (LOAD (mword_of_int 96, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (VDT + 0x22)%Z (mword_of_int 0x53bc : mword 16)
    (mword_of_int (VDT + 0x22) : mword 64) (LOAD (mword_of_int 96, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) vtc_53bc vte_53bc. Qed.

  Lemma vti_24 : kernel_text -∗ instr (mword_of_int (VDT + 0x24) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_rvc (VDT + 0x24)%Z (mword_of_int 0x8b8d : mword 16)
    (mword_of_int (VDT + 0x24) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) vtc_8b8d vte_8b8d. Qed.

  Lemma vti_26 : kernel_text -∗ instr (mword_of_int (VDT + 0x26) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 14), LUI)).
  Proof. mk_base (VDT + 0x26)%Z (mword_of_int 0x10001737 : mword 32)
    (mword_of_int (VDT + 0x26) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 14), LUI)) bdec_10001737. Qed.

  Lemma vti_2a : kernel_text -∗ instr (mword_of_int (VDT + 0x2a) : mword 64) true (STORE (mword_of_int 100, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)).
  Proof. mk_rvc (VDT + 0x2a)%Z (mword_of_int 0xd37c : mword 16)
    (mword_of_int (VDT + 0x2a) : mword 64) (STORE (mword_of_int 100, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)) vtc_d37c vte_d37c. Qed.

  Lemma vti_2c : kernel_text -∗ instr (mword_of_int (VDT + 0x2c) : mword 64) false (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))).
  Proof. mk_base (VDT + 0x2c)%Z (mword_of_int 0x0330000f : mword 32)
    (mword_of_int (VDT + 0x2c) : mword 64) (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))) bdec_0330000f. Qed.

  (* ---- the loop-entry test ---- *)
  Lemma vti_30 : kernel_text -∗ instr (mword_of_int (VDT + 0x30) : mword 64) true (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc (VDT + 0x30)%Z (mword_of_int 0x689c : mword 16)
    (mword_of_int (VDT + 0x30) : mword 64) (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)) cdec_689c vte_689c. Qed.

  Lemma vti_32 : kernel_text -∗ instr (mword_of_int (VDT + 0x32) : mword 64) false (LOAD (mword_of_int 32 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), true, 2)).
  Proof. mk_base (VDT + 0x32)%Z (mword_of_int 0x0204d703 : mword 32)
    (mword_of_int (VDT + 0x32) : mword 64) (LOAD (mword_of_int 32 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), true, 2)) vtb_0204d703. Qed.

  Lemma vti_36 : kernel_text -∗ instr (mword_of_int (VDT + 0x36) : mword 64) false (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 2)).
  Proof. mk_base (VDT + 0x36)%Z (mword_of_int 0x0027d783 : mword 32)
    (mword_of_int (VDT + 0x36) : mword 64) (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 2)) vtb_0027d783. Qed.

  Lemma vti_3a : kernel_text -∗ instr (mword_of_int (VDT + 0x3a) : mword 64) false (BTYPE (mword_of_int 80 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)).
  Proof. mk_base (VDT + 0x3a)%Z (mword_of_int 0x04f70863 : mword 32)
    (mword_of_int (VDT + 0x3a) : mword 64) (BTYPE (mword_of_int 80 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)) bdec_04f70863. Qed.

  (* ---- the loop body ---- *)
  Lemma vti_3e : kernel_text -∗ instr (mword_of_int (VDT + 0x3e) : mword 64) false (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))).
  Proof. mk_base (VDT + 0x3e)%Z (mword_of_int 0x0330000f : mword 32)
    (mword_of_int (VDT + 0x3e) : mword 64) (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))) bdec_0330000f. Qed.

  Lemma vti_42 : kernel_text -∗ instr (mword_of_int (VDT + 0x42) : mword 64) true (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 8)).
  Proof. mk_rvc (VDT + 0x42)%Z (mword_of_int 0x6898 : mword 16)
    (mword_of_int (VDT + 0x42) : mword 64) (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 8)) vtc_6898 vte_6898. Qed.

  Lemma vti_44 : kernel_text -∗ instr (mword_of_int (VDT + 0x44) : mword 64) false (LOAD (mword_of_int 32 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), true, 2)).
  Proof. mk_base (VDT + 0x44)%Z (mword_of_int 0x0204d783 : mword 32)
    (mword_of_int (VDT + 0x44) : mword 64) (LOAD (mword_of_int 32 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), true, 2)) vtb_0204d783. Qed.

  Lemma vti_48 : kernel_text -∗ instr (mword_of_int (VDT + 0x48) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 7 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_rvc (VDT + 0x48)%Z (mword_of_int 0x8b9d : mword 16)
    (mword_of_int (VDT + 0x48) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 7 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) vtc_8b9d vte_8b9d. Qed.

  Lemma vti_4a : kernel_text -∗ instr (mword_of_int (VDT + 0x4a) : mword 64) true (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (VDT + 0x4a)%Z (mword_of_int 0x078e : mword 16)
    (mword_of_int (VDT + 0x4a) : mword 64) (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) cdec_078e exec_execute_C_SLLI. Qed.

  Lemma vti_4c : kernel_text -∗ instr (mword_of_int (VDT + 0x4c) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (VDT + 0x4c)%Z (mword_of_int 0x97ba : mword 16)
    (mword_of_int (VDT + 0x4c) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97ba exec_execute_C_ADD. Qed.

  Lemma vti_4e : kernel_text -∗ instr (mword_of_int (VDT + 0x4e) : mword 64) true (LOAD (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (VDT + 0x4e)%Z (mword_of_int 0x43dc : mword 16)
    (mword_of_int (VDT + 0x4e) : mword 64) (LOAD (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) cdec_43dc vte_43dc. Qed.

  Lemma vti_50 : kernel_text -∗ instr (mword_of_int (VDT + 0x50) : mword 64) false (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 14), SLLI)).
  Proof. mk_base (VDT + 0x50)%Z (mword_of_int 0x00479713 : mword 32)
    (mword_of_int (VDT + 0x50) : mword 64) (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 14), SLLI)) vtb_00479713. Qed.

  Lemma vti_54 : kernel_text -∗ instr (mword_of_int (VDT + 0x54) : mword 64) false (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (VDT + 0x54)%Z (mword_of_int 0x02070713 : mword 32)
    (mword_of_int (VDT + 0x54) : mword 64) (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) bdec_02070713. Qed.

  Lemma vti_58 : kernel_text -∗ instr (mword_of_int (VDT + 0x58) : mword 64) true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (VDT + 0x58)%Z (mword_of_int 0x9726 : mword 16)
    (mword_of_int (VDT + 0x58) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)) cdec_9726 exec_execute_C_ADD. Qed.

  Lemma vti_5a : kernel_text -∗ instr (mword_of_int (VDT + 0x5a) : mword 64) false (LOAD (mword_of_int 16 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), true, 1)).
  Proof. mk_base (VDT + 0x5a)%Z (mword_of_int 0x01074703 : mword 32)
    (mword_of_int (VDT + 0x5a) : mword 64) (LOAD (mword_of_int 16 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), true, 1)) vtb_01074703. Qed.

  Lemma vti_5e : kernel_text -∗ instr (mword_of_int (VDT + 0x5e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 33 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BNE)).
  Proof. mk_rvc (VDT + 0x5e)%Z (mword_of_int 0xe329 : mword 16)
    (mword_of_int (VDT + 0x5e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 33 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BNE)) vtc_e329 exec_execute_C_BNEZ. Qed.

  Lemma vti_60 : kernel_text -∗ instr (mword_of_int (VDT + 0x60) : mword 64) true (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (VDT + 0x60)%Z (mword_of_int 0x0792 : mword 16)
    (mword_of_int (VDT + 0x60) : mword 64) (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) vtc_0792 exec_execute_C_SLLI. Qed.

  Lemma vti_62 : kernel_text -∗ instr (mword_of_int (VDT + 0x62) : mword 64) false (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (VDT + 0x62)%Z (mword_of_int 0x02078793 : mword 32)
    (mword_of_int (VDT + 0x62) : mword 64) (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) vtb_02078793. Qed.

  Lemma vti_66 : kernel_text -∗ instr (mword_of_int (VDT + 0x66) : mword 64) true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (VDT + 0x66)%Z (mword_of_int 0x97a6 : mword 16)
    (mword_of_int (VDT + 0x66) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97a6 exec_execute_C_ADD. Qed.

  Lemma vti_68 : kernel_text -∗ instr (mword_of_int (VDT + 0x68) : mword 64) true (LOAD (mword_of_int 8, Regidx (mword_of_int 15), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_rvc (VDT + 0x68)%Z (mword_of_int 0x6788 : mword 16)
    (mword_of_int (VDT + 0x68) : mword 64) (LOAD (mword_of_int 8, Regidx (mword_of_int 15), Regidx (mword_of_int 10), false, 8)) vtc_6788 vte_6788. Qed.

  Lemma vti_6a : kernel_text -∗ instr (mword_of_int (VDT + 0x6a) : mword 64) false (STORE (mword_of_int 4 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4)).
  Proof. mk_base (VDT + 0x6a)%Z (mword_of_int 0x00052223 : mword 32)
    (mword_of_int (VDT + 0x6a) : mword 64) (STORE (mword_of_int 4 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4)) vtb_00052223. Qed.

  Lemma vti_6e : kernel_text -∗ instr (mword_of_int (VDT + 0x6e) : mword 64) false (JAL (mword_of_int 2082178 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VDT + 0x6e)%Z (mword_of_int 0xd82fc0ef : mword 32)
    (mword_of_int (VDT + 0x6e) : mword 64) (JAL (mword_of_int 2082178 : mword 21, Regidx (mword_of_int 1))) vtb_d82fc0ef. Qed.

  (* ---- disk.used_idx += 1 (with the 16-bit wrap) ---- *)
  Lemma vti_72 : kernel_text -∗ instr (mword_of_int (VDT + 0x72) : mword 64) false (LOAD (mword_of_int 32 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), true, 2)).
  Proof. mk_base (VDT + 0x72)%Z (mword_of_int 0x0204d783 : mword 32)
    (mword_of_int (VDT + 0x72) : mword 64) (LOAD (mword_of_int 32 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), true, 2)) vtb_0204d783. Qed.

  Lemma vti_76 : kernel_text -∗ instr (mword_of_int (VDT + 0x76) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (VDT + 0x76)%Z (mword_of_int 0x2785 : mword 16)
    (mword_of_int (VDT + 0x76) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2785 exec_execute_C_ADDIW. Qed.

  Lemma vti_78 : kernel_text -∗ instr (mword_of_int (VDT + 0x78) : mword 64) true (SHIFTIOP (mword_of_int 48 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (VDT + 0x78)%Z (mword_of_int 0x17c2 : mword 16)
    (mword_of_int (VDT + 0x78) : mword 64) (SHIFTIOP (mword_of_int 48 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) vtc_17c2 exec_execute_C_SLLI. Qed.

  Lemma vti_7a : kernel_text -∗ instr (mword_of_int (VDT + 0x7a) : mword 64) true (SHIFTIOP (mword_of_int 48 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)).
  Proof. mk_rvc (VDT + 0x7a)%Z (mword_of_int 0x93c1 : mword 16)
    (mword_of_int (VDT + 0x7a) : mword 64) (SHIFTIOP (mword_of_int 48 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)) vtc_93c1 exec_execute_C_SRLI. Qed.

  Lemma vti_7c : kernel_text -∗ instr (mword_of_int (VDT + 0x7c) : mword 64) false (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 2)).
  Proof. mk_base (VDT + 0x7c)%Z (mword_of_int 0x02f49023 : mword 32)
    (mword_of_int (VDT + 0x7c) : mword 64) (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 2)) vtb_02f49023. Qed.

  (* ---- the loop-back test ---- *)
  Lemma vti_80 : kernel_text -∗ instr (mword_of_int (VDT + 0x80) : mword 64) true (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 8)).
  Proof. mk_rvc (VDT + 0x80)%Z (mword_of_int 0x6898 : mword 16)
    (mword_of_int (VDT + 0x80) : mword 64) (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 8)) vtc_6898 vte_6898. Qed.

  Lemma vti_82 : kernel_text -∗ instr (mword_of_int (VDT + 0x82) : mword 64) false (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), true, 2)).
  Proof. mk_base (VDT + 0x82)%Z (mword_of_int 0x00275703 : mword 32)
    (mword_of_int (VDT + 0x82) : mword 64) (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), true, 2)) vtb_00275703. Qed.

  Lemma vti_86 : kernel_text -∗ instr (mword_of_int (VDT + 0x86) : mword 64) false (BTYPE (mword_of_int 8120 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE)).
  Proof. mk_base (VDT + 0x86)%Z (mword_of_int 0xfaf71ce3 : mword 32)
    (mword_of_int (VDT + 0x86) : mword 64) (BTYPE (mword_of_int 8120 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE)) vtb_faf71ce3. Qed.

  (* ---- release and epilogue ---- *)
  Lemma vti_8a : kernel_text -∗ instr (mword_of_int (VDT + 0x8a) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (VDT + 0x8a)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (VDT + 0x8a) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  Lemma vti_8e : kernel_text -∗ instr (mword_of_int (VDT + 0x8e) : mword 64) false (ITYPE (mword_of_int 0xb54 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (VDT + 0x8e)%Z (mword_of_int 0xb5450513 : mword 32)
    (mword_of_int (VDT + 0x8e) : mword 64) (ITYPE (mword_of_int 0xb54 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) vtb_b5450513. Qed.

  Lemma vti_92 : kernel_text -∗ instr (mword_of_int (VDT + 0x92) : mword 64) false (JAL (mword_of_int 2077340 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VDT + 0x92)%Z (mword_of_int 0xa9cfb0ef : mword 32)
    (mword_of_int (VDT + 0x92) : mword 64) (JAL (mword_of_int 2077340 : mword 21, Regidx (mword_of_int 1))) vtb_a9cfb0ef. Qed.

  Lemma vti_96 : kernel_text -∗ instr (mword_of_int (VDT + 0x96) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (VDT + 0x96)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (VDT + 0x96) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma vti_98 : kernel_text -∗ instr (mword_of_int (VDT + 0x98) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (VDT + 0x98)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (VDT + 0x98) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma vti_9a : kernel_text -∗ instr (mword_of_int (VDT + 0x9a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (VDT + 0x9a)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (VDT + 0x9a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma vti_9c : kernel_text -∗ instr (mword_of_int (VDT + 0x9c) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (VDT + 0x9c)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (VDT + 0x9c) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma vti_9e : kernel_text -∗ instr (mword_of_int (VDT + 0x9e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (VDT + 0x9e)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (VDT + 0x9e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End VirtioDiskIntrInstrs.
