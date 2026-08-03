(* CodeVirtioDiskRw.v -- the instruction-DECODE layer for xv6's
   virtio_disk_rw().  For every instruction of

     virtio_disk_rw @ 0x80005750 .. 0x80005960   (offsets 0x000 .. 0x210)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([rwi_<off>]).

   The function is 172 instructions long and contains three loops (the
   descriptor-allocation retry loop with its inner 8-way scan, the
   completion-wait sleep loop, and the free_chain walk), so the [instr]
   facts for the loop bodies are used at more than one program point; the
   decode layer is address-keyed and knows nothing of that.

   Layout of the generated names:
     [rwc_<word>] : compressed decode  (exec (ext_decode_compressed w) s = ...)
     [rwe_<word>] : the C_* -> base expansion for the compressed loads/stores
                    and the two bit-ops, specialised to concrete registers
     [rwb_<word>] : base (4-byte) decode
     [rwi_<off>]  : the per-address [instr] fact
   Words already carried by KernelRvcDecode.v / KernelBaseDecode.v are
   reused ([cdec_*] / [bdec_*]) rather than re-proved. *)
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

Notation VRW := KernelSyms.virtio_disk_rw.

(* ===================================================================== *)
(* Compressed decodes.                                                    *)
(* ===================================================================== *)














Lemma rwc_8b2e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8b2e : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 22), Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_1b82 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1b82 : mword 16)) s
  = Some (C_SLLI (mword_of_int 32, Regidx (mword_of_int 23)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_44a1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x44a1 : mword 16)) s
  = Some (C_LI (mword_of_int 8, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_4a0d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4a0d : mword 16)) s
  = Some (C_LI (mword_of_int 3, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_5c7d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x5c7d : mword 16)) s
  = Some (C_LI (mword_of_int 63, Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_a095 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa095 : mword 16)) s
  = Some (C_J (mword_of_int 50), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_c19c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc19c : mword 16)) s
  = Some (C_SW (mword_of_int 0, Cregidx (mword_of_int 3), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.


Lemma rwc_0611 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0611 : mword 16)) s
  = Some (C_ADDI (mword_of_int 4, Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.


Lemma rwc_fee9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xfee9 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 237, Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.




Lemma rwc_973e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x973e : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 14), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_c710 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc710 : mword 16)) s
  = Some (C_SW (mword_of_int 2, Cregidx (mword_of_int 6), Cregidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.




Lemma rwc_e310 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe310 : mword 16)) s
  = Some (C_SD (mword_of_int 0, Cregidx (mword_of_int 6), Cregidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_6390 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6390 : mword 16)) s
  = Some (C_LD (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_4741 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4741 : mword 16)) s
  = Some (C_LI (mword_of_int 16, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_0712 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0712 : mword 16)) s
  = Some (C_SLLI (mword_of_int 4, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_963a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x963a : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 12), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_9746 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9746 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 14), Regidx (mword_of_int 17)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_8e4d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8e4d : mword 16)) s
  = Some (C_OR (Cregidx (mword_of_int 4), Cregidx (mword_of_int 3)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_983e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x983e : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 16), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.


Lemma rwc_0612 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0612 : mword 16)) s
  = Some (C_SLLI (mword_of_int 4, Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_98b2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x98b2 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 17), Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_9732 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9732 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 14), Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_c70c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc70c : mword 16)) s
  = Some (C_SW (mword_of_int 2, Cregidx (mword_of_int 6), Cregidx (mword_of_int 3)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_4689 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4689 : mword 16)) s
  = Some (C_LI (mword_of_int 2, Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_6794 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6794 : mword 16)) s
  = Some (C_LD (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_8b1d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8b1d : mword 16)) s
  = Some (C_ANDI (mword_of_int 7, Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_0706 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0706 : mword 16)) s
  = Some (C_SLLI (mword_of_int 1, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_96ba s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x96ba : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 13), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_6798 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6798 : mword 16)) s
  = Some (C_LD (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.



Lemma rwc_8885 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8885 : mword 16)) s
  = Some (C_ANDI (mword_of_int 1, Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma rwc_f0fd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf0fd : mword 16)) s
  = Some (C_BNEZ (mword_of_int 243, Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.













(* ---- C_* -> base expansions at this function's concrete operands ---- *)

Lemma rwe_c19c s :
  exec (execute (C_SW (mword_of_int 0, Cregidx (mword_of_int 3), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 11), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma rwe_c710 s :
  exec (execute (C_SW (mword_of_int 2, Cregidx (mword_of_int 6), Cregidx (mword_of_int 4)))) s
  = Some (ExecuteAs (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma rwe_6398 s :
  exec (execute (C_LD (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma rwe_e310 s :
  exec (execute (C_SD (mword_of_int 0, Cregidx (mword_of_int 6), Cregidx (mword_of_int 4)))) s
  = Some (ExecuteAs (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma rwe_6390 s :
  exec (execute (C_LD (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 4)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 12), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma rwe_8e4d s :
  exec (execute (C_OR (Cregidx (mword_of_int 4), Cregidx (mword_of_int 3)))) s
  = Some (ExecuteAs (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 12), Regidx (mword_of_int 12), OR)), s).
Proof. apply exec_execute_C_OR_leaf; vm_compute; reflexivity. Qed.

Lemma rwe_c70c s :
  exec (execute (C_SW (mword_of_int 2, Cregidx (mword_of_int 6), Cregidx (mword_of_int 3)))) s
  = Some (ExecuteAs (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 14), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma rwe_6794 s :
  exec (execute (C_LD (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 5)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma rwe_8b1d s :
  exec (execute (C_ANDI (mword_of_int 7, Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 (mword_of_int 7 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ANDI)), s).
Proof. apply exec_execute_C_ANDI_leaf; vm_compute; reflexivity. Qed.

Lemma rwe_6798 s :
  exec (execute (C_LD (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma rwe_8885 s :
  exec (execute (C_ANDI (mword_of_int 1, Cregidx (mword_of_int 1)))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ANDI)), s).
Proof. apply exec_execute_C_ANDI_leaf; vm_compute; reflexivity. Qed.


(* ===================================================================== *)
(* Base (4-byte) decodes.                                                 *)
(* ===================================================================== *)

(* [decode_bridge_ms] closes its concrete-decode obligation with a bare
   [reflexivity], which needs the two sides' bitvector well-formedness
   PROOF TERMS to coincide.  For [fence rw,rw] -- the only word here whose
   AST carries [mword 4] literals -- they do not, so that one word uses
   WpDecodeBridge's [decode_bridge_ms_bv], the same bridge with the
   [bv_eq]-per-leaf closing of [rvc_oneshot]. *)

Lemma rwb_00c52b83 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00c52b83 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 12 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 23), false, 4), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_001b9b9b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x001b9b9b : mword 32) : M instruction) s
  = Some (SHIFTIWOP (mword_of_int 1 : mword 5, Regidx (mword_of_int 23), Regidx (mword_of_int 23), SLLIW), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_020bdb93 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x020bdb93 : mword 32) : M instruction) s
  = Some (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 23), Regidx (mword_of_int 23), SRLI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_dc650513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xdc650513 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 3526 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_c86fb0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc86fb0ef : mword 32) : M instruction) s
  = Some (JAL (mword_of_int 2077830 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0001ea97 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001ea97 : mword 32) : M instruction) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 21), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_c90a8a93 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc90a8a93 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 3216 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00fa8733 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00fa8733 : mword 32) : M instruction) s
  = Some (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 21), Regidx (mword_of_int 14), ADD), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00070c23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00070c23 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0207c563 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0207c563 : mword 32) : M instruction) s
  = Some (BTYPE (mword_of_int 42 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BLT), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_05490c63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05490c63 : mword 32) : M instruction) s
  = Some (BTYPE (mword_of_int 88 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 18), BEQ), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_c6a70713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc6a70713 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 3178 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_01874683 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01874683 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 13), true, 1), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_fe979be3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfe979be3 : mword 32) : M instruction) s
  = Some (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 15), BNE), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0185a023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0185a023 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 24), Regidx (mword_of_int 11), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_01205d63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01205d63 : mword 32) : M instruction) s
  = Some (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 0), BGE), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_fa042503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfa042503 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 4000 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 4), s).
Proof. decode_bridge_ms. Qed.


Lemma rwb_0127d663 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0127d663 : mword 32) : M instruction) s
  = Some (BTYPE (mword_of_int 12 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 15), BGE), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_fa442503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfa442503 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 4004 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 4), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_d33ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd33ff0ef : mword 32) : M instruction) s
  = Some (JAL (mword_of_int 2096434 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0001e597 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e597 : mword 32) : M instruction) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_d5c58593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd5c58593 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 3420 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_c4450513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc4450513 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 3140 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_f12fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf12fc0ef : mword 32) : M instruction) s
  = Some (JAL (mword_of_int 2082578 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_fa040613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfa040613 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 4000 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI), s).
Proof. decode_bridge_ms. Qed.


Lemma rwb_c1078793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc1078793 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 3088 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00451713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00451713 : mword 32) : M instruction) s
  = Some (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 14), SLLI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0a070713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0a070713 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 160 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_01603633 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01603633 : mword 32) : M instruction) s
  = Some (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 0), Regidx (mword_of_int 12), SLTU), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00072623 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00072623 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_01773823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01773823 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 23), Regidx (mword_of_int 14), 8), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0a868613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0a868613 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 168 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 12), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00d60833 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00d60833 : mword 32) : M instruction) s
  = Some (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 12), Regidx (mword_of_int 16), ADD), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00e82423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e82423 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 16), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00b81623 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00b81623 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 16), 2), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_fa442703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfa442703 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 4004 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00e81723 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e81723 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 14 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 16), 2), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_05898813 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05898813 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 16), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_01063023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01063023 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 16), Regidx (mword_of_int 12), 8), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0007b883 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007b883 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 17), false, 8), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_40000613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40000613 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 1024 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 12), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_001b3613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x001b3613 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 12), SLTIU), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0016161b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0016161b : mword 32) : M instruction) s
  = Some (SHIFTIWOP (mword_of_int 1 : mword 5, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLIW), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00c71623 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00c71623 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 2), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_fa842603 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfa842603 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 4008 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), false, 4), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00c71723 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00c71723 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 14 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 2), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00451813 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00451813 : mword 32) : M instruction) s
  = Some (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 16), SLLI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_02080813 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02080813 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 16), Regidx (mword_of_int 16), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00e80823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e80823 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 16), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_03068713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03068713 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 48 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00e8b023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e8b023 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 17), 8), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00d71623 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00d71623 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 2), s).
Proof. decode_bridge_ms. Qed.


Lemma rwb_00b9a223 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00b9a223 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 4 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 19), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_01383423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01383423 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 16), 8), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0026d703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0026d703 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), true, 2), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00a69223 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00a69223 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 4 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 13), 2), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00275783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00275783 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), true, 2), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00f71123 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f71123 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 2), s).
Proof. decode_bridge_ms. Qed.


Lemma rwb_0407a823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0407a823 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 80 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0049a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0049a783 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 4 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0001e917 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e917 : mword 32) : M instruction) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 18), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_c5e90913 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc5e90913 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 3166 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00b79a63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00b79a63 : mword 32) : M instruction) s
  = Some (BTYPE (mword_of_int 20 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BNE), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_e12fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe12fc0ef : mword 32) : M instruction) s
  = Some (JAL (mword_of_int 2082322 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_fe978ae3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfe978ae3 : mword 32) : M instruction) s
  = Some (BTYPE (mword_of_int 8180 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 15), BEQ), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_fa042903 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfa042903 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 4000 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 18), false, 4), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00491713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00491713 : mword 32) : M instruction) s
  = Some (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 18), Regidx (mword_of_int 14), SLLI), s).
Proof. decode_bridge_ms. Qed.


Lemma rwb_b0c78793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb0c78793 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 2828 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0007b423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007b423 : mword 32) : M instruction) s
  = Some (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 8), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0001e997 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e997 : mword 32) : M instruction) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 19), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_afe98993 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xafe98993 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 2814 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_0009b783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0009b783 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), false, 8), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00c7d483 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00c7d483 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 12 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), true, 2), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_00e7d903 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e7d903 : mword 32) : M instruction) s
  = Some (LOAD (mword_of_int 14 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 18), true, 2), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_bddff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xbddff0ef : mword 32) : M instruction) s
  = Some (JAL (mword_of_int 2096092 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_c0250513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc0250513 : mword 32) : M instruction) s
  = Some (ITYPE (mword_of_int 3074 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma rwb_b4afb0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb4afb0ef : mword 32) : M instruction) s
  = Some (JAL (mword_of_int 2077514 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.


(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section VirtioDiskRwInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma rwi_000 : kernel_text -∗ instr (mword_of_int (VRW + 0x000) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 58 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (VRW + 0x000)%Z (mword_of_int 0x711d : mword 16)
    (mword_of_int (VRW + 0x000) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 58 : mword 6), sp, sp, ADDI)) cdec_711d exec_execute_C_ADDI16SP. Qed.

  Lemma rwi_002 : kernel_text -∗ instr (mword_of_int (VRW + 0x002) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (VRW + 0x002)%Z (mword_of_int 0xec86 : mword 16)
    (mword_of_int (VRW + 0x002) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec86 exec_execute_C_SDSP. Qed.

  Lemma rwi_004 : kernel_text -∗ instr (mword_of_int (VRW + 0x004) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (VRW + 0x004)%Z (mword_of_int 0xe8a2 : mword 16)
    (mword_of_int (VRW + 0x004) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e8a2 exec_execute_C_SDSP. Qed.

  Lemma rwi_006 : kernel_text -∗ instr (mword_of_int (VRW + 0x006) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (VRW + 0x006)%Z (mword_of_int 0xe4a6 : mword 16)
    (mword_of_int (VRW + 0x006) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e4a6 exec_execute_C_SDSP. Qed.

  Lemma rwi_008 : kernel_text -∗ instr (mword_of_int (VRW + 0x008) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (VRW + 0x008)%Z (mword_of_int 0xe0ca : mword 16)
    (mword_of_int (VRW + 0x008) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e0ca exec_execute_C_SDSP. Qed.

  Lemma rwi_00a : kernel_text -∗ instr (mword_of_int (VRW + 0x00a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (VRW + 0x00a)%Z (mword_of_int 0xfc4e : mword 16)
    (mword_of_int (VRW + 0x00a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_fc4e exec_execute_C_SDSP. Qed.

  Lemma rwi_00c : kernel_text -∗ instr (mword_of_int (VRW + 0x00c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (VRW + 0x00c)%Z (mword_of_int 0xf852 : mword 16)
    (mword_of_int (VRW + 0x00c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_f852 exec_execute_C_SDSP. Qed.

  Lemma rwi_00e : kernel_text -∗ instr (mword_of_int (VRW + 0x00e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (VRW + 0x00e)%Z (mword_of_int 0xf456 : mword 16)
    (mword_of_int (VRW + 0x00e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_f456 exec_execute_C_SDSP. Qed.

  Lemma rwi_010 : kernel_text -∗ instr (mword_of_int (VRW + 0x010) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (VRW + 0x010)%Z (mword_of_int 0xf05a : mword 16)
    (mword_of_int (VRW + 0x010) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_f05a exec_execute_C_SDSP. Qed.

  Lemma rwi_012 : kernel_text -∗ instr (mword_of_int (VRW + 0x012) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).
  Proof. mk_rvc (VRW + 0x012)%Z (mword_of_int 0xec5e : mword 16)
    (mword_of_int (VRW + 0x012) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) cdec_ec5e exec_execute_C_SDSP. Qed.

  Lemma rwi_014 : kernel_text -∗ instr (mword_of_int (VRW + 0x014) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)).
  Proof. mk_rvc (VRW + 0x014)%Z (mword_of_int 0xe862 : mword 16)
    (mword_of_int (VRW + 0x014) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)) cdec_e862 exec_execute_C_SDSP. Qed.

  Lemma rwi_016 : kernel_text -∗ instr (mword_of_int (VRW + 0x016) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 24 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (VRW + 0x016)%Z (mword_of_int 0x1080 : mword 16)
    (mword_of_int (VRW + 0x016) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 24 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1080 exec_execute_C_ADDI4SPN. Qed.

  Lemma rwi_018 : kernel_text -∗ instr (mword_of_int (VRW + 0x018) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (VRW + 0x018)%Z (mword_of_int 0x89aa : mword 16)
    (mword_of_int (VRW + 0x018) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)) cdec_89aa exec_execute_C_MV. Qed.

  Lemma rwi_01a : kernel_text -∗ instr (mword_of_int (VRW + 0x01a) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 22), ADD)).
  Proof. mk_rvc (VRW + 0x01a)%Z (mword_of_int 0x8b2e : mword 16)
    (mword_of_int (VRW + 0x01a) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 22), ADD)) rwc_8b2e exec_execute_C_MV. Qed.

  Lemma rwi_01c : kernel_text -∗ instr (mword_of_int (VRW + 0x01c) : mword 64) false (LOAD (mword_of_int 12 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 23), false, 4)).
  Proof. mk_base (VRW + 0x01c)%Z (mword_of_int 0x00c52b83 : mword 32)
    (mword_of_int (VRW + 0x01c) : mword 64) (LOAD (mword_of_int 12 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 23), false, 4)) rwb_00c52b83. Qed.

  Lemma rwi_020 : kernel_text -∗ instr (mword_of_int (VRW + 0x020) : mword 64) false (SHIFTIWOP (mword_of_int 1 : mword 5, Regidx (mword_of_int 23), Regidx (mword_of_int 23), SLLIW)).
  Proof. mk_base (VRW + 0x020)%Z (mword_of_int 0x001b9b9b : mword 32)
    (mword_of_int (VRW + 0x020) : mword 64) (SHIFTIWOP (mword_of_int 1 : mword 5, Regidx (mword_of_int 23), Regidx (mword_of_int 23), SLLIW)) rwb_001b9b9b. Qed.

  Lemma rwi_024 : kernel_text -∗ instr (mword_of_int (VRW + 0x024) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 23), Regidx (mword_of_int 23), SLLI)).
  Proof. mk_rvc (VRW + 0x024)%Z (mword_of_int 0x1b82 : mword 16)
    (mword_of_int (VRW + 0x024) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 23), Regidx (mword_of_int 23), SLLI)) rwc_1b82 exec_execute_C_SLLI. Qed.

  Lemma rwi_026 : kernel_text -∗ instr (mword_of_int (VRW + 0x026) : mword 64) false (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 23), Regidx (mword_of_int 23), SRLI)).
  Proof. mk_base (VRW + 0x026)%Z (mword_of_int 0x020bdb93 : mword 32)
    (mword_of_int (VRW + 0x026) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 23), Regidx (mword_of_int 23), SRLI)) rwb_020bdb93. Qed.

  Lemma rwi_02a : kernel_text -∗ instr (mword_of_int (VRW + 0x02a) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (VRW + 0x02a)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (VRW + 0x02a) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  Lemma rwi_02e : kernel_text -∗ instr (mword_of_int (VRW + 0x02e) : mword 64) false (ITYPE (mword_of_int 3526 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (VRW + 0x02e)%Z (mword_of_int 0xdc650513 : mword 32)
    (mword_of_int (VRW + 0x02e) : mword 64) (ITYPE (mword_of_int 3526 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) rwb_dc650513. Qed.

  Lemma rwi_032 : kernel_text -∗ instr (mword_of_int (VRW + 0x032) : mword 64) false (JAL (mword_of_int 2077830 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VRW + 0x032)%Z (mword_of_int 0xc86fb0ef : mword 32)
    (mword_of_int (VRW + 0x032) : mword 64) (JAL (mword_of_int 2077830 : mword 21, Regidx (mword_of_int 1))) rwb_c86fb0ef. Qed.

  Lemma rwi_036 : kernel_text -∗ instr (mword_of_int (VRW + 0x036) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)).
  Proof. mk_rvc (VRW + 0x036)%Z (mword_of_int 0x44a1 : mword 16)
    (mword_of_int (VRW + 0x036) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)) rwc_44a1 exec_execute_C_LI. Qed.

  Lemma rwi_038 : kernel_text -∗ instr (mword_of_int (VRW + 0x038) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 21), AUIPC)).
  Proof. mk_base (VRW + 0x038)%Z (mword_of_int 0x0001ea97 : mword 32)
    (mword_of_int (VRW + 0x038) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 21), AUIPC)) rwb_0001ea97. Qed.

  Lemma rwi_03c : kernel_text -∗ instr (mword_of_int (VRW + 0x03c) : mword 64) false (ITYPE (mword_of_int 3216 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI)).
  Proof. mk_base (VRW + 0x03c)%Z (mword_of_int 0xc90a8a93 : mword 32)
    (mword_of_int (VRW + 0x03c) : mword 64) (ITYPE (mword_of_int 3216 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI)) rwb_c90a8a93. Qed.

  Lemma rwi_040 : kernel_text -∗ instr (mword_of_int (VRW + 0x040) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 20), ADDI)).
  Proof. mk_rvc (VRW + 0x040)%Z (mword_of_int 0x4a0d : mword 16)
    (mword_of_int (VRW + 0x040) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 20), ADDI)) rwc_4a0d exec_execute_C_LI. Qed.

  Lemma rwi_042 : kernel_text -∗ instr (mword_of_int (VRW + 0x042) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 24), ADDI)).
  Proof. mk_rvc (VRW + 0x042)%Z (mword_of_int 0x5c7d : mword 16)
    (mword_of_int (VRW + 0x042) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 24), ADDI)) rwc_5c7d exec_execute_C_LI. Qed.

  Lemma rwi_044 : kernel_text -∗ instr (mword_of_int (VRW + 0x044) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 50 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (VRW + 0x044)%Z (mword_of_int 0xa095 : mword 16)
    (mword_of_int (VRW + 0x044) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 50 : mword 11) ('b"0")), zreg)) rwc_a095 exec_execute_C_J. Qed.

  Lemma rwi_046 : kernel_text -∗ instr (mword_of_int (VRW + 0x046) : mword 64) false (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 21), Regidx (mword_of_int 14), ADD)).
  Proof. mk_base (VRW + 0x046)%Z (mword_of_int 0x00fa8733 : mword 32)
    (mword_of_int (VRW + 0x046) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 21), Regidx (mword_of_int 14), ADD)) rwb_00fa8733. Qed.

  Lemma rwi_04a : kernel_text -∗ instr (mword_of_int (VRW + 0x04a) : mword 64) false (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 1)).
  Proof. mk_base (VRW + 0x04a)%Z (mword_of_int 0x00070c23 : mword 32)
    (mword_of_int (VRW + 0x04a) : mword 64) (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 1)) rwb_00070c23. Qed.

  Lemma rwi_04e : kernel_text -∗ instr (mword_of_int (VRW + 0x04e) : mword 64) true (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 11), 4)).
  Proof. mk_rvc (VRW + 0x04e)%Z (mword_of_int 0xc19c : mword 16)
    (mword_of_int (VRW + 0x04e) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 11), 4)) rwc_c19c rwe_c19c. Qed.

  Lemma rwi_050 : kernel_text -∗ instr (mword_of_int (VRW + 0x050) : mword 64) false (BTYPE (mword_of_int 42 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BLT)).
  Proof. mk_base (VRW + 0x050)%Z (mword_of_int 0x0207c563 : mword 32)
    (mword_of_int (VRW + 0x050) : mword 64) (BTYPE (mword_of_int 42 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BLT)) rwb_0207c563. Qed.

  Lemma rwi_054 : kernel_text -∗ instr (mword_of_int (VRW + 0x054) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 18), Regidx (mword_of_int 18))).
  Proof. mk_rvc (VRW + 0x054)%Z (mword_of_int 0x2905 : mword 16)
    (mword_of_int (VRW + 0x054) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 18), Regidx (mword_of_int 18))) cdec_2905 exec_execute_C_ADDIW. Qed.

  Lemma rwi_056 : kernel_text -∗ instr (mword_of_int (VRW + 0x056) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (VRW + 0x056)%Z (mword_of_int 0x0611 : mword 16)
    (mword_of_int (VRW + 0x056) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)) rwc_0611 exec_execute_C_ADDI. Qed.

  Lemma rwi_058 : kernel_text -∗ instr (mword_of_int (VRW + 0x058) : mword 64) false (BTYPE (mword_of_int 88 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 18), BEQ)).
  Proof. mk_base (VRW + 0x058)%Z (mword_of_int 0x05490c63 : mword 32)
    (mword_of_int (VRW + 0x058) : mword 64) (BTYPE (mword_of_int 88 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 18), BEQ)) rwb_05490c63. Qed.

  Lemma rwi_05c : kernel_text -∗ instr (mword_of_int (VRW + 0x05c) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (VRW + 0x05c)%Z (mword_of_int 0x85b2 : mword 16)
    (mword_of_int (VRW + 0x05c) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 11), ADD)) cdec_85b2 exec_execute_C_MV. Qed.

  Lemma rwi_05e : kernel_text -∗ instr (mword_of_int (VRW + 0x05e) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (VRW + 0x05e)%Z (mword_of_int 0x0001e717 : mword 32)
    (mword_of_int (VRW + 0x05e) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)) bdec_0001e717. Qed.

  Lemma rwi_062 : kernel_text -∗ instr (mword_of_int (VRW + 0x062) : mword 64) false (ITYPE (mword_of_int 3178 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (VRW + 0x062)%Z (mword_of_int 0xc6a70713 : mword 32)
    (mword_of_int (VRW + 0x062) : mword 64) (ITYPE (mword_of_int 3178 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) rwb_c6a70713. Qed.

  Lemma rwi_066 : kernel_text -∗ instr (mword_of_int (VRW + 0x066) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (VRW + 0x066)%Z (mword_of_int 0x4781 : mword 16)
    (mword_of_int (VRW + 0x066) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4781 exec_execute_C_LI. Qed.

  Lemma rwi_068 : kernel_text -∗ instr (mword_of_int (VRW + 0x068) : mword 64) false (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 13), true, 1)).
  Proof. mk_base (VRW + 0x068)%Z (mword_of_int 0x01874683 : mword 32)
    (mword_of_int (VRW + 0x068) : mword 64) (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 13), true, 1)) rwb_01874683. Qed.

  Lemma rwi_06c : kernel_text -∗ instr (mword_of_int (VRW + 0x06c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 237 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 5)), BNE)).
  Proof. mk_rvc (VRW + 0x06c)%Z (mword_of_int 0xfee9 : mword 16)
    (mword_of_int (VRW + 0x06c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 237 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 5)), BNE)) rwc_fee9 exec_execute_C_BNEZ. Qed.

  Lemma rwi_06e : kernel_text -∗ instr (mword_of_int (VRW + 0x06e) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (VRW + 0x06e)%Z (mword_of_int 0x2785 : mword 16)
    (mword_of_int (VRW + 0x06e) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2785 exec_execute_C_ADDIW. Qed.

  Lemma rwi_070 : kernel_text -∗ instr (mword_of_int (VRW + 0x070) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (VRW + 0x070)%Z (mword_of_int 0x0705 : mword 16)
    (mword_of_int (VRW + 0x070) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) cdec_0705 exec_execute_C_ADDI. Qed.

  Lemma rwi_072 : kernel_text -∗ instr (mword_of_int (VRW + 0x072) : mword 64) false (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (VRW + 0x072)%Z (mword_of_int 0xfe979be3 : mword 32)
    (mword_of_int (VRW + 0x072) : mword 64) (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 15), BNE)) rwb_fe979be3. Qed.

  Lemma rwi_076 : kernel_text -∗ instr (mword_of_int (VRW + 0x076) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 24), Regidx (mword_of_int 11), 4)).
  Proof. mk_base (VRW + 0x076)%Z (mword_of_int 0x0185a023 : mword 32)
    (mword_of_int (VRW + 0x076) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 24), Regidx (mword_of_int 11), 4)) rwb_0185a023. Qed.

  Lemma rwi_07a : kernel_text -∗ instr (mword_of_int (VRW + 0x07a) : mword 64) false (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (VRW + 0x07a)%Z (mword_of_int 0x01205d63 : mword 32)
    (mword_of_int (VRW + 0x07a) : mword 64) (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 0), BGE)) rwb_01205d63. Qed.

  Lemma rwi_07e : kernel_text -∗ instr (mword_of_int (VRW + 0x07e) : mword 64) false (LOAD (mword_of_int 4000 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_base (VRW + 0x07e)%Z (mword_of_int 0xfa042503 : mword 32)
    (mword_of_int (VRW + 0x07e) : mword 64) (LOAD (mword_of_int 4000 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 4)) rwb_fa042503. Qed.

  Lemma rwi_082 : kernel_text -∗ instr (mword_of_int (VRW + 0x082) : mword 64) false (JAL (mword_of_int 2096448 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VRW + 0x082)%Z (mword_of_int 0xd41ff0ef : mword 32)
    (mword_of_int (VRW + 0x082) : mword 64) (JAL (mword_of_int 2096448 : mword 21, Regidx (mword_of_int 1))) bdec_d41ff0ef. Qed.

  Lemma rwi_086 : kernel_text -∗ instr (mword_of_int (VRW + 0x086) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (VRW + 0x086)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (VRW + 0x086) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.

  Lemma rwi_088 : kernel_text -∗ instr (mword_of_int (VRW + 0x088) : mword 64) false (BTYPE (mword_of_int 12 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 15), BGE)).
  Proof. mk_base (VRW + 0x088)%Z (mword_of_int 0x0127d663 : mword 32)
    (mword_of_int (VRW + 0x088) : mword 64) (BTYPE (mword_of_int 12 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 15), BGE)) rwb_0127d663. Qed.

  Lemma rwi_08c : kernel_text -∗ instr (mword_of_int (VRW + 0x08c) : mword 64) false (LOAD (mword_of_int 4004 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_base (VRW + 0x08c)%Z (mword_of_int 0xfa442503 : mword 32)
    (mword_of_int (VRW + 0x08c) : mword 64) (LOAD (mword_of_int 4004 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 4)) rwb_fa442503. Qed.

  Lemma rwi_090 : kernel_text -∗ instr (mword_of_int (VRW + 0x090) : mword 64) false (JAL (mword_of_int 2096434 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VRW + 0x090)%Z (mword_of_int 0xd33ff0ef : mword 32)
    (mword_of_int (VRW + 0x090) : mword 64) (JAL (mword_of_int 2096434 : mword 21, Regidx (mword_of_int 1))) rwb_d33ff0ef. Qed.

  Lemma rwi_094 : kernel_text -∗ instr (mword_of_int (VRW + 0x094) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (VRW + 0x094)%Z (mword_of_int 0x0001e597 : mword 32)
    (mword_of_int (VRW + 0x094) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 11), AUIPC)) rwb_0001e597. Qed.

  Lemma rwi_098 : kernel_text -∗ instr (mword_of_int (VRW + 0x098) : mword 64) false (ITYPE (mword_of_int 3420 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (VRW + 0x098)%Z (mword_of_int 0xd5c58593 : mword 32)
    (mword_of_int (VRW + 0x098) : mword 64) (ITYPE (mword_of_int 3420 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) rwb_d5c58593. Qed.

  Lemma rwi_09c : kernel_text -∗ instr (mword_of_int (VRW + 0x09c) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (VRW + 0x09c)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (VRW + 0x09c) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  Lemma rwi_0a0 : kernel_text -∗ instr (mword_of_int (VRW + 0x0a0) : mword 64) false (ITYPE (mword_of_int 3140 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (VRW + 0x0a0)%Z (mword_of_int 0xc4450513 : mword 32)
    (mword_of_int (VRW + 0x0a0) : mword 64) (ITYPE (mword_of_int 3140 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) rwb_c4450513. Qed.

  Lemma rwi_0a4 : kernel_text -∗ instr (mword_of_int (VRW + 0x0a4) : mword 64) false (JAL (mword_of_int 2082578 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VRW + 0x0a4)%Z (mword_of_int 0xf12fc0ef : mword 32)
    (mword_of_int (VRW + 0x0a4) : mword 64) (JAL (mword_of_int 2082578 : mword 21, Regidx (mword_of_int 1))) rwb_f12fc0ef. Qed.

  Lemma rwi_0a8 : kernel_text -∗ instr (mword_of_int (VRW + 0x0a8) : mword 64) false (ITYPE (mword_of_int 4000 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (VRW + 0x0a8)%Z (mword_of_int 0xfa040613 : mword 32)
    (mword_of_int (VRW + 0x0a8) : mword 64) (ITYPE (mword_of_int 4000 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI)) rwb_fa040613. Qed.

  Lemma rwi_0ac : kernel_text -∗ instr (mword_of_int (VRW + 0x0ac) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 18), ADDI)).
  Proof. mk_rvc (VRW + 0x0ac)%Z (mword_of_int 0x4901 : mword 16)
    (mword_of_int (VRW + 0x0ac) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 18), ADDI)) cdec_4901 exec_execute_C_LI. Qed.

  Lemma rwi_0ae : kernel_text -∗ instr (mword_of_int (VRW + 0x0ae) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (VRW + 0x0ae)%Z (mword_of_int 0xb77d : mword 16)
    (mword_of_int (VRW + 0x0ae) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0")), zreg)) cdec_b77d exec_execute_C_J. Qed.

  Lemma rwi_0b0 : kernel_text -∗ instr (mword_of_int (VRW + 0x0b0) : mword 64) false (LOAD (mword_of_int 4000 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_base (VRW + 0x0b0)%Z (mword_of_int 0xfa042503 : mword 32)
    (mword_of_int (VRW + 0x0b0) : mword 64) (LOAD (mword_of_int 4000 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 4)) rwb_fa042503. Qed.

  Lemma rwi_0b4 : kernel_text -∗ instr (mword_of_int (VRW + 0x0b4) : mword 64) false (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 13), SLLI)).
  Proof. mk_base (VRW + 0x0b4)%Z (mword_of_int 0x00451693 : mword 32)
    (mword_of_int (VRW + 0x0b4) : mword 64) (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 13), SLLI)) bdec_00451693. Qed.

  Lemma rwi_0b8 : kernel_text -∗ instr (mword_of_int (VRW + 0x0b8) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (VRW + 0x0b8)%Z (mword_of_int 0x0001e797 : mword 32)
    (mword_of_int (VRW + 0x0b8) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0001e797. Qed.

  Lemma rwi_0bc : kernel_text -∗ instr (mword_of_int (VRW + 0x0bc) : mword 64) false (ITYPE (mword_of_int 3088 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (VRW + 0x0bc)%Z (mword_of_int 0xc1078793 : mword 32)
    (mword_of_int (VRW + 0x0bc) : mword 64) (ITYPE (mword_of_int 3088 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) rwb_c1078793. Qed.

  Lemma rwi_0c0 : kernel_text -∗ instr (mword_of_int (VRW + 0x0c0) : mword 64) false (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 14), SLLI)).
  Proof. mk_base (VRW + 0x0c0)%Z (mword_of_int 0x00451713 : mword 32)
    (mword_of_int (VRW + 0x0c0) : mword 64) (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 14), SLLI)) rwb_00451713. Qed.

  Lemma rwi_0c4 : kernel_text -∗ instr (mword_of_int (VRW + 0x0c4) : mword 64) false (ITYPE (mword_of_int 160 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (VRW + 0x0c4)%Z (mword_of_int 0x0a070713 : mword 32)
    (mword_of_int (VRW + 0x0c4) : mword 64) (ITYPE (mword_of_int 160 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) rwb_0a070713. Qed.

  Lemma rwi_0c8 : kernel_text -∗ instr (mword_of_int (VRW + 0x0c8) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (VRW + 0x0c8)%Z (mword_of_int 0x973e : mword 16)
    (mword_of_int (VRW + 0x0c8) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)) rwc_973e exec_execute_C_ADD. Qed.

  Lemma rwi_0ca : kernel_text -∗ instr (mword_of_int (VRW + 0x0ca) : mword 64) false (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 0), Regidx (mword_of_int 12), SLTU)).
  Proof. mk_base (VRW + 0x0ca)%Z (mword_of_int 0x01603633 : mword 32)
    (mword_of_int (VRW + 0x0ca) : mword 64) (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 0), Regidx (mword_of_int 12), SLTU)) rwb_01603633. Qed.

  Lemma rwi_0ce : kernel_text -∗ instr (mword_of_int (VRW + 0x0ce) : mword 64) true (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 4)).
  Proof. mk_rvc (VRW + 0x0ce)%Z (mword_of_int 0xc710 : mword 16)
    (mword_of_int (VRW + 0x0ce) : mword 64) (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 4)) rwc_c710 rwe_c710. Qed.

  Lemma rwi_0d0 : kernel_text -∗ instr (mword_of_int (VRW + 0x0d0) : mword 64) false (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 4)).
  Proof. mk_base (VRW + 0x0d0)%Z (mword_of_int 0x00072623 : mword 32)
    (mword_of_int (VRW + 0x0d0) : mword 64) (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 4)) rwb_00072623. Qed.

  Lemma rwi_0d4 : kernel_text -∗ instr (mword_of_int (VRW + 0x0d4) : mword 64) false (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 23), Regidx (mword_of_int 14), 8)).
  Proof. mk_base (VRW + 0x0d4)%Z (mword_of_int 0x01773823 : mword 32)
    (mword_of_int (VRW + 0x0d4) : mword 64) (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 23), Regidx (mword_of_int 14), 8)) rwb_01773823. Qed.

  Lemma rwi_0d8 : kernel_text -∗ instr (mword_of_int (VRW + 0x0d8) : mword 64) true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)).
  Proof. mk_rvc (VRW + 0x0d8)%Z (mword_of_int 0x6398 : mword 16)
    (mword_of_int (VRW + 0x0d8) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)) cdec_6398 rwe_6398. Qed.

  Lemma rwi_0da : kernel_text -∗ instr (mword_of_int (VRW + 0x0da) : mword 64) true (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (VRW + 0x0da)%Z (mword_of_int 0x9736 : mword 16)
    (mword_of_int (VRW + 0x0da) : mword 64) (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)) cdec_9736 exec_execute_C_ADD. Qed.

  Lemma rwi_0dc : kernel_text -∗ instr (mword_of_int (VRW + 0x0dc) : mword 64) false (ITYPE (mword_of_int 168 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (VRW + 0x0dc)%Z (mword_of_int 0x0a868613 : mword 32)
    (mword_of_int (VRW + 0x0dc) : mword 64) (ITYPE (mword_of_int 168 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 12), ADDI)) rwb_0a868613. Qed.

  Lemma rwi_0e0 : kernel_text -∗ instr (mword_of_int (VRW + 0x0e0) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (VRW + 0x0e0)%Z (mword_of_int 0x963e : mword 16)
    (mword_of_int (VRW + 0x0e0) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADD)) cdec_963e exec_execute_C_ADD. Qed.

  Lemma rwi_0e2 : kernel_text -∗ instr (mword_of_int (VRW + 0x0e2) : mword 64) true (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 8)).
  Proof. mk_rvc (VRW + 0x0e2)%Z (mword_of_int 0xe310 : mword 16)
    (mword_of_int (VRW + 0x0e2) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 8)) rwc_e310 rwe_e310. Qed.

  Lemma rwi_0e4 : kernel_text -∗ instr (mword_of_int (VRW + 0x0e4) : mword 64) true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 12), false, 8)).
  Proof. mk_rvc (VRW + 0x0e4)%Z (mword_of_int 0x6390 : mword 16)
    (mword_of_int (VRW + 0x0e4) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 12), false, 8)) rwc_6390 rwe_6390. Qed.

  Lemma rwi_0e6 : kernel_text -∗ instr (mword_of_int (VRW + 0x0e6) : mword 64) false (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 12), Regidx (mword_of_int 16), ADD)).
  Proof. mk_base (VRW + 0x0e6)%Z (mword_of_int 0x00d60833 : mword 32)
    (mword_of_int (VRW + 0x0e6) : mword 64) (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 12), Regidx (mword_of_int 16), ADD)) rwb_00d60833. Qed.

  Lemma rwi_0ea : kernel_text -∗ instr (mword_of_int (VRW + 0x0ea) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (VRW + 0x0ea)%Z (mword_of_int 0x4741 : mword 16)
    (mword_of_int (VRW + 0x0ea) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) rwc_4741 exec_execute_C_LI. Qed.

  Lemma rwi_0ec : kernel_text -∗ instr (mword_of_int (VRW + 0x0ec) : mword 64) false (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 16), 4)).
  Proof. mk_base (VRW + 0x0ec)%Z (mword_of_int 0x00e82423 : mword 32)
    (mword_of_int (VRW + 0x0ec) : mword 64) (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 16), 4)) rwb_00e82423. Qed.

  Lemma rwi_0f0 : kernel_text -∗ instr (mword_of_int (VRW + 0x0f0) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (VRW + 0x0f0)%Z (mword_of_int 0x4585 : mword 16)
    (mword_of_int (VRW + 0x0f0) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4585 exec_execute_C_LI. Qed.

  Lemma rwi_0f2 : kernel_text -∗ instr (mword_of_int (VRW + 0x0f2) : mword 64) false (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 16), 2)).
  Proof. mk_base (VRW + 0x0f2)%Z (mword_of_int 0x00b81623 : mword 32)
    (mword_of_int (VRW + 0x0f2) : mword 64) (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 16), 2)) rwb_00b81623. Qed.

  Lemma rwi_0f6 : kernel_text -∗ instr (mword_of_int (VRW + 0x0f6) : mword 64) false (LOAD (mword_of_int 4004 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_base (VRW + 0x0f6)%Z (mword_of_int 0xfa442703 : mword 32)
    (mword_of_int (VRW + 0x0f6) : mword 64) (LOAD (mword_of_int 4004 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4)) rwb_fa442703. Qed.

  Lemma rwi_0fa : kernel_text -∗ instr (mword_of_int (VRW + 0x0fa) : mword 64) false (STORE (mword_of_int 14 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 16), 2)).
  Proof. mk_base (VRW + 0x0fa)%Z (mword_of_int 0x00e81723 : mword 32)
    (mword_of_int (VRW + 0x0fa) : mword 64) (STORE (mword_of_int 14 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 16), 2)) rwb_00e81723. Qed.

  Lemma rwi_0fe : kernel_text -∗ instr (mword_of_int (VRW + 0x0fe) : mword 64) true (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLLI)).
  Proof. mk_rvc (VRW + 0x0fe)%Z (mword_of_int 0x0712 : mword 16)
    (mword_of_int (VRW + 0x0fe) : mword 64) (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLLI)) rwc_0712 exec_execute_C_SLLI. Qed.

  Lemma rwi_100 : kernel_text -∗ instr (mword_of_int (VRW + 0x100) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (VRW + 0x100)%Z (mword_of_int 0x963a : mword 16)
    (mword_of_int (VRW + 0x100) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADD)) rwc_963a exec_execute_C_ADD. Qed.

  Lemma rwi_102 : kernel_text -∗ instr (mword_of_int (VRW + 0x102) : mword 64) false (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 16), ADDI)).
  Proof. mk_base (VRW + 0x102)%Z (mword_of_int 0x05898813 : mword 32)
    (mword_of_int (VRW + 0x102) : mword 64) (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 16), ADDI)) rwb_05898813. Qed.

  Lemma rwi_106 : kernel_text -∗ instr (mword_of_int (VRW + 0x106) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 16), Regidx (mword_of_int 12), 8)).
  Proof. mk_base (VRW + 0x106)%Z (mword_of_int 0x01063023 : mword 32)
    (mword_of_int (VRW + 0x106) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 16), Regidx (mword_of_int 12), 8)) rwb_01063023. Qed.

  Lemma rwi_10a : kernel_text -∗ instr (mword_of_int (VRW + 0x10a) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 17), false, 8)).
  Proof. mk_base (VRW + 0x10a)%Z (mword_of_int 0x0007b883 : mword 32)
    (mword_of_int (VRW + 0x10a) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 17), false, 8)) rwb_0007b883. Qed.

  Lemma rwi_10e : kernel_text -∗ instr (mword_of_int (VRW + 0x10e) : mword 64) true (RTYPE (Regidx (mword_of_int 17), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (VRW + 0x10e)%Z (mword_of_int 0x9746 : mword 16)
    (mword_of_int (VRW + 0x10e) : mword 64) (RTYPE (Regidx (mword_of_int 17), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)) rwc_9746 exec_execute_C_ADD. Qed.

  Lemma rwi_110 : kernel_text -∗ instr (mword_of_int (VRW + 0x110) : mword 64) false (ITYPE (mword_of_int 1024 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (VRW + 0x110)%Z (mword_of_int 0x40000613 : mword 32)
    (mword_of_int (VRW + 0x110) : mword 64) (ITYPE (mword_of_int 1024 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 12), ADDI)) rwb_40000613. Qed.

  Lemma rwi_114 : kernel_text -∗ instr (mword_of_int (VRW + 0x114) : mword 64) true (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 4)).
  Proof. mk_rvc (VRW + 0x114)%Z (mword_of_int 0xc710 : mword 16)
    (mword_of_int (VRW + 0x114) : mword 64) (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 4)) rwc_c710 rwe_c710. Qed.

  Lemma rwi_116 : kernel_text -∗ instr (mword_of_int (VRW + 0x116) : mword 64) false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 12), SLTIU)).
  Proof. mk_base (VRW + 0x116)%Z (mword_of_int 0x001b3613 : mword 32)
    (mword_of_int (VRW + 0x116) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 12), SLTIU)) rwb_001b3613. Qed.

  Lemma rwi_11a : kernel_text -∗ instr (mword_of_int (VRW + 0x11a) : mword 64) false (SHIFTIWOP (mword_of_int 1 : mword 5, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLIW)).
  Proof. mk_base (VRW + 0x11a)%Z (mword_of_int 0x0016161b : mword 32)
    (mword_of_int (VRW + 0x11a) : mword 64) (SHIFTIWOP (mword_of_int 1 : mword 5, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLIW)) rwb_0016161b. Qed.

  Lemma rwi_11e : kernel_text -∗ instr (mword_of_int (VRW + 0x11e) : mword 64) true (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 12), Regidx (mword_of_int 12), OR)).
  Proof. mk_rvc (VRW + 0x11e)%Z (mword_of_int 0x8e4d : mword 16)
    (mword_of_int (VRW + 0x11e) : mword 64) (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 12), Regidx (mword_of_int 12), OR)) rwc_8e4d rwe_8e4d. Qed.

  Lemma rwi_120 : kernel_text -∗ instr (mword_of_int (VRW + 0x120) : mword 64) false (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 2)).
  Proof. mk_base (VRW + 0x120)%Z (mword_of_int 0x00c71623 : mword 32)
    (mword_of_int (VRW + 0x120) : mword 64) (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 2)) rwb_00c71623. Qed.

  Lemma rwi_124 : kernel_text -∗ instr (mword_of_int (VRW + 0x124) : mword 64) false (LOAD (mword_of_int 4008 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), false, 4)).
  Proof. mk_base (VRW + 0x124)%Z (mword_of_int 0xfa842603 : mword 32)
    (mword_of_int (VRW + 0x124) : mword 64) (LOAD (mword_of_int 4008 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), false, 4)) rwb_fa842603. Qed.

  Lemma rwi_128 : kernel_text -∗ instr (mword_of_int (VRW + 0x128) : mword 64) false (STORE (mword_of_int 14 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 2)).
  Proof. mk_base (VRW + 0x128)%Z (mword_of_int 0x00c71723 : mword 32)
    (mword_of_int (VRW + 0x128) : mword 64) (STORE (mword_of_int 14 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 2)) rwb_00c71723. Qed.

  Lemma rwi_12c : kernel_text -∗ instr (mword_of_int (VRW + 0x12c) : mword 64) false (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 16), SLLI)).
  Proof. mk_base (VRW + 0x12c)%Z (mword_of_int 0x00451813 : mword 32)
    (mword_of_int (VRW + 0x12c) : mword 64) (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 16), SLLI)) rwb_00451813. Qed.

  Lemma rwi_130 : kernel_text -∗ instr (mword_of_int (VRW + 0x130) : mword 64) false (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 16), Regidx (mword_of_int 16), ADDI)).
  Proof. mk_base (VRW + 0x130)%Z (mword_of_int 0x02080813 : mword 32)
    (mword_of_int (VRW + 0x130) : mword 64) (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 16), Regidx (mword_of_int 16), ADDI)) rwb_02080813. Qed.

  Lemma rwi_134 : kernel_text -∗ instr (mword_of_int (VRW + 0x134) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 16), Regidx (mword_of_int 16), ADD)).
  Proof. mk_rvc (VRW + 0x134)%Z (mword_of_int 0x983e : mword 16)
    (mword_of_int (VRW + 0x134) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 16), Regidx (mword_of_int 16), ADD)) rwc_983e exec_execute_C_ADD. Qed.

  Lemma rwi_136 : kernel_text -∗ instr (mword_of_int (VRW + 0x136) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (VRW + 0x136)%Z (mword_of_int 0x577d : mword 16)
    (mword_of_int (VRW + 0x136) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) cdec_577d exec_execute_C_LI. Qed.

  Lemma rwi_138 : kernel_text -∗ instr (mword_of_int (VRW + 0x138) : mword 64) false (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 16), 1)).
  Proof. mk_base (VRW + 0x138)%Z (mword_of_int 0x00e80823 : mword 32)
    (mword_of_int (VRW + 0x138) : mword 64) (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 16), 1)) rwb_00e80823. Qed.

  Lemma rwi_13c : kernel_text -∗ instr (mword_of_int (VRW + 0x13c) : mword 64) true (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)).
  Proof. mk_rvc (VRW + 0x13c)%Z (mword_of_int 0x0612 : mword 16)
    (mword_of_int (VRW + 0x13c) : mword 64) (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)) rwc_0612 exec_execute_C_SLLI. Qed.

  Lemma rwi_13e : kernel_text -∗ instr (mword_of_int (VRW + 0x13e) : mword 64) true (RTYPE (Regidx (mword_of_int 12), Regidx (mword_of_int 17), Regidx (mword_of_int 17), ADD)).
  Proof. mk_rvc (VRW + 0x13e)%Z (mword_of_int 0x98b2 : mword 16)
    (mword_of_int (VRW + 0x13e) : mword 64) (RTYPE (Regidx (mword_of_int 12), Regidx (mword_of_int 17), Regidx (mword_of_int 17), ADD)) rwc_98b2 exec_execute_C_ADD. Qed.

  Lemma rwi_140 : kernel_text -∗ instr (mword_of_int (VRW + 0x140) : mword 64) false (ITYPE (mword_of_int 48 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (VRW + 0x140)%Z (mword_of_int 0x03068713 : mword 32)
    (mword_of_int (VRW + 0x140) : mword 64) (ITYPE (mword_of_int 48 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), ADDI)) rwb_03068713. Qed.

  Lemma rwi_144 : kernel_text -∗ instr (mword_of_int (VRW + 0x144) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (VRW + 0x144)%Z (mword_of_int 0x973e : mword 16)
    (mword_of_int (VRW + 0x144) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)) rwc_973e exec_execute_C_ADD. Qed.

  Lemma rwi_146 : kernel_text -∗ instr (mword_of_int (VRW + 0x146) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 17), 8)).
  Proof. mk_base (VRW + 0x146)%Z (mword_of_int 0x00e8b023 : mword 32)
    (mword_of_int (VRW + 0x146) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 17), 8)) rwb_00e8b023. Qed.

  Lemma rwi_14a : kernel_text -∗ instr (mword_of_int (VRW + 0x14a) : mword 64) true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)).
  Proof. mk_rvc (VRW + 0x14a)%Z (mword_of_int 0x6398 : mword 16)
    (mword_of_int (VRW + 0x14a) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)) cdec_6398 rwe_6398. Qed.

  Lemma rwi_14c : kernel_text -∗ instr (mword_of_int (VRW + 0x14c) : mword 64) true (RTYPE (Regidx (mword_of_int 12), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (VRW + 0x14c)%Z (mword_of_int 0x9732 : mword 16)
    (mword_of_int (VRW + 0x14c) : mword 64) (RTYPE (Regidx (mword_of_int 12), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)) rwc_9732 exec_execute_C_ADD. Qed.

  Lemma rwi_14e : kernel_text -∗ instr (mword_of_int (VRW + 0x14e) : mword 64) true (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 14), 4)).
  Proof. mk_rvc (VRW + 0x14e)%Z (mword_of_int 0xc70c : mword 16)
    (mword_of_int (VRW + 0x14e) : mword 64) (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 14), 4)) rwc_c70c rwe_c70c. Qed.

  Lemma rwi_150 : kernel_text -∗ instr (mword_of_int (VRW + 0x150) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)).
  Proof. mk_rvc (VRW + 0x150)%Z (mword_of_int 0x4689 : mword 16)
    (mword_of_int (VRW + 0x150) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)) rwc_4689 exec_execute_C_LI. Qed.

  Lemma rwi_152 : kernel_text -∗ instr (mword_of_int (VRW + 0x152) : mword 64) false (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 2)).
  Proof. mk_base (VRW + 0x152)%Z (mword_of_int 0x00d71623 : mword 32)
    (mword_of_int (VRW + 0x152) : mword 64) (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 2)) rwb_00d71623. Qed.

  Lemma rwi_156 : kernel_text -∗ instr (mword_of_int (VRW + 0x156) : mword 64) false (STORE (mword_of_int 14 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 2)).
  Proof. mk_base (VRW + 0x156)%Z (mword_of_int 0x00071723 : mword 32)
    (mword_of_int (VRW + 0x156) : mword 64) (STORE (mword_of_int 14 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 2)) bdec_00071723. Qed.

  Lemma rwi_15a : kernel_text -∗ instr (mword_of_int (VRW + 0x15a) : mword 64) false (STORE (mword_of_int 4 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 19), 4)).
  Proof. mk_base (VRW + 0x15a)%Z (mword_of_int 0x00b9a223 : mword 32)
    (mword_of_int (VRW + 0x15a) : mword 64) (STORE (mword_of_int 4 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 19), 4)) rwb_00b9a223. Qed.

  Lemma rwi_15e : kernel_text -∗ instr (mword_of_int (VRW + 0x15e) : mword 64) false (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 16), 8)).
  Proof. mk_base (VRW + 0x15e)%Z (mword_of_int 0x01383423 : mword 32)
    (mword_of_int (VRW + 0x15e) : mword 64) (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 16), 8)) rwb_01383423. Qed.

  Lemma rwi_162 : kernel_text -∗ instr (mword_of_int (VRW + 0x162) : mword 64) true (LOAD (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13), false, 8)).
  Proof. mk_rvc (VRW + 0x162)%Z (mword_of_int 0x6794 : mword 16)
    (mword_of_int (VRW + 0x162) : mword 64) (LOAD (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13), false, 8)) rwc_6794 rwe_6794. Qed.

  Lemma rwi_164 : kernel_text -∗ instr (mword_of_int (VRW + 0x164) : mword 64) false (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), true, 2)).
  Proof. mk_base (VRW + 0x164)%Z (mword_of_int 0x0026d703 : mword 32)
    (mword_of_int (VRW + 0x164) : mword 64) (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), true, 2)) rwb_0026d703. Qed.

  Lemma rwi_168 : kernel_text -∗ instr (mword_of_int (VRW + 0x168) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 7 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ANDI)).
  Proof. mk_rvc (VRW + 0x168)%Z (mword_of_int 0x8b1d : mword 16)
    (mword_of_int (VRW + 0x168) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 7 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ANDI)) rwc_8b1d rwe_8b1d. Qed.

  Lemma rwi_16a : kernel_text -∗ instr (mword_of_int (VRW + 0x16a) : mword 64) true (SHIFTIOP (mword_of_int 1 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLLI)).
  Proof. mk_rvc (VRW + 0x16a)%Z (mword_of_int 0x0706 : mword 16)
    (mword_of_int (VRW + 0x16a) : mword 64) (SHIFTIOP (mword_of_int 1 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLLI)) rwc_0706 exec_execute_C_SLLI. Qed.

  Lemma rwi_16c : kernel_text -∗ instr (mword_of_int (VRW + 0x16c) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADD)).
  Proof. mk_rvc (VRW + 0x16c)%Z (mword_of_int 0x96ba : mword 16)
    (mword_of_int (VRW + 0x16c) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADD)) rwc_96ba exec_execute_C_ADD. Qed.

  Lemma rwi_16e : kernel_text -∗ instr (mword_of_int (VRW + 0x16e) : mword 64) false (STORE (mword_of_int 4 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 13), 2)).
  Proof. mk_base (VRW + 0x16e)%Z (mword_of_int 0x00a69223 : mword 32)
    (mword_of_int (VRW + 0x16e) : mword 64) (STORE (mword_of_int 4 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 13), 2)) rwb_00a69223. Qed.

  Lemma rwi_172 : kernel_text -∗ instr (mword_of_int (VRW + 0x172) : mword 64) false (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))).
  Proof. mk_base (VRW + 0x172)%Z (mword_of_int 0x0330000f : mword 32)
    (mword_of_int (VRW + 0x172) : mword 64) (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))) bdec_0330000f. Qed.

  Lemma rwi_176 : kernel_text -∗ instr (mword_of_int (VRW + 0x176) : mword 64) true (LOAD (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)).
  Proof. mk_rvc (VRW + 0x176)%Z (mword_of_int 0x6798 : mword 16)
    (mword_of_int (VRW + 0x176) : mword 64) (LOAD (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)) rwc_6798 rwe_6798. Qed.

  Lemma rwi_178 : kernel_text -∗ instr (mword_of_int (VRW + 0x178) : mword 64) false (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), true, 2)).
  Proof. mk_base (VRW + 0x178)%Z (mword_of_int 0x00275783 : mword 32)
    (mword_of_int (VRW + 0x178) : mword 64) (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), true, 2)) rwb_00275783. Qed.

  Lemma rwi_17c : kernel_text -∗ instr (mword_of_int (VRW + 0x17c) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (VRW + 0x17c)%Z (mword_of_int 0x2785 : mword 16)
    (mword_of_int (VRW + 0x17c) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2785 exec_execute_C_ADDIW. Qed.

  Lemma rwi_17e : kernel_text -∗ instr (mword_of_int (VRW + 0x17e) : mword 64) false (STORE (mword_of_int 2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 2)).
  Proof. mk_base (VRW + 0x17e)%Z (mword_of_int 0x00f71123 : mword 32)
    (mword_of_int (VRW + 0x17e) : mword 64) (STORE (mword_of_int 2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 2)) rwb_00f71123. Qed.

  Lemma rwi_182 : kernel_text -∗ instr (mword_of_int (VRW + 0x182) : mword 64) false (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))).
  Proof. mk_base (VRW + 0x182)%Z (mword_of_int 0x0330000f : mword 32)
    (mword_of_int (VRW + 0x182) : mword 64) (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))) bdec_0330000f. Qed.

  Lemma rwi_186 : kernel_text -∗ instr (mword_of_int (VRW + 0x186) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (VRW + 0x186)%Z (mword_of_int 0x100017b7 : mword 32)
    (mword_of_int (VRW + 0x186) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)) bdec_100017b7. Qed.

  Lemma rwi_18a : kernel_text -∗ instr (mword_of_int (VRW + 0x18a) : mword 64) false (STORE (mword_of_int 80 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)).
  Proof. mk_base (VRW + 0x18a)%Z (mword_of_int 0x0407a823 : mword 32)
    (mword_of_int (VRW + 0x18a) : mword 64) (STORE (mword_of_int 80 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)) rwb_0407a823. Qed.

  Lemma rwi_18e : kernel_text -∗ instr (mword_of_int (VRW + 0x18e) : mword 64) false (LOAD (mword_of_int 4 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (VRW + 0x18e)%Z (mword_of_int 0x0049a783 : mword 32)
    (mword_of_int (VRW + 0x18e) : mword 64) (LOAD (mword_of_int 4 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), false, 4)) rwb_0049a783. Qed.

  Lemma rwi_192 : kernel_text -∗ instr (mword_of_int (VRW + 0x192) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 18), AUIPC)).
  Proof. mk_base (VRW + 0x192)%Z (mword_of_int 0x0001e917 : mword 32)
    (mword_of_int (VRW + 0x192) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 18), AUIPC)) rwb_0001e917. Qed.

  Lemma rwi_196 : kernel_text -∗ instr (mword_of_int (VRW + 0x196) : mword 64) false (ITYPE (mword_of_int 3166 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (VRW + 0x196)%Z (mword_of_int 0xc5e90913 : mword 32)
    (mword_of_int (VRW + 0x196) : mword 64) (ITYPE (mword_of_int 3166 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) rwb_c5e90913. Qed.

  Lemma rwi_19a : kernel_text -∗ instr (mword_of_int (VRW + 0x19a) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (VRW + 0x19a)%Z (mword_of_int 0x84ae : mword 16)
    (mword_of_int (VRW + 0x19a) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)) cdec_84ae exec_execute_C_MV. Qed.

  Lemma rwi_19c : kernel_text -∗ instr (mword_of_int (VRW + 0x19c) : mword 64) false (BTYPE (mword_of_int 20 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (VRW + 0x19c)%Z (mword_of_int 0x00b79a63 : mword 32)
    (mword_of_int (VRW + 0x19c) : mword 64) (BTYPE (mword_of_int 20 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BNE)) rwb_00b79a63. Qed.

  Lemma rwi_1a0 : kernel_text -∗ instr (mword_of_int (VRW + 0x1a0) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (VRW + 0x1a0)%Z (mword_of_int 0x85ca : mword 16)
    (mword_of_int (VRW + 0x1a0) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ca exec_execute_C_MV. Qed.

  Lemma rwi_1a2 : kernel_text -∗ instr (mword_of_int (VRW + 0x1a2) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (VRW + 0x1a2)%Z (mword_of_int 0x854e : mword 16)
    (mword_of_int (VRW + 0x1a2) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)) cdec_854e exec_execute_C_MV. Qed.

  Lemma rwi_1a4 : kernel_text -∗ instr (mword_of_int (VRW + 0x1a4) : mword 64) false (JAL (mword_of_int 2082322 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VRW + 0x1a4)%Z (mword_of_int 0xe12fc0ef : mword 32)
    (mword_of_int (VRW + 0x1a4) : mword 64) (JAL (mword_of_int 2082322 : mword 21, Regidx (mword_of_int 1))) rwb_e12fc0ef. Qed.

  Lemma rwi_1a8 : kernel_text -∗ instr (mword_of_int (VRW + 0x1a8) : mword 64) false (LOAD (mword_of_int 4 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (VRW + 0x1a8)%Z (mword_of_int 0x0049a783 : mword 32)
    (mword_of_int (VRW + 0x1a8) : mword 64) (LOAD (mword_of_int 4 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), false, 4)) rwb_0049a783. Qed.

  Lemma rwi_1ac : kernel_text -∗ instr (mword_of_int (VRW + 0x1ac) : mword 64) false (BTYPE (mword_of_int 8180 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 15), BEQ)).
  Proof. mk_base (VRW + 0x1ac)%Z (mword_of_int 0xfe978ae3 : mword 32)
    (mword_of_int (VRW + 0x1ac) : mword 64) (BTYPE (mword_of_int 8180 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 15), BEQ)) rwb_fe978ae3. Qed.

  Lemma rwi_1b0 : kernel_text -∗ instr (mword_of_int (VRW + 0x1b0) : mword 64) false (LOAD (mword_of_int 4000 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 18), false, 4)).
  Proof. mk_base (VRW + 0x1b0)%Z (mword_of_int 0xfa042903 : mword 32)
    (mword_of_int (VRW + 0x1b0) : mword 64) (LOAD (mword_of_int 4000 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 18), false, 4)) rwb_fa042903. Qed.

  Lemma rwi_1b4 : kernel_text -∗ instr (mword_of_int (VRW + 0x1b4) : mword 64) false (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 18), Regidx (mword_of_int 14), SLLI)).
  Proof. mk_base (VRW + 0x1b4)%Z (mword_of_int 0x00491713 : mword 32)
    (mword_of_int (VRW + 0x1b4) : mword 64) (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 18), Regidx (mword_of_int 14), SLLI)) rwb_00491713. Qed.

  Lemma rwi_1b8 : kernel_text -∗ instr (mword_of_int (VRW + 0x1b8) : mword 64) false (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (VRW + 0x1b8)%Z (mword_of_int 0x02070713 : mword 32)
    (mword_of_int (VRW + 0x1b8) : mword 64) (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) bdec_02070713. Qed.

  Lemma rwi_1bc : kernel_text -∗ instr (mword_of_int (VRW + 0x1bc) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (VRW + 0x1bc)%Z (mword_of_int 0x0001e797 : mword 32)
    (mword_of_int (VRW + 0x1bc) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0001e797. Qed.

  Lemma rwi_1c0 : kernel_text -∗ instr (mword_of_int (VRW + 0x1c0) : mword 64) false (ITYPE (mword_of_int 2828 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (VRW + 0x1c0)%Z (mword_of_int 0xb0c78793 : mword 32)
    (mword_of_int (VRW + 0x1c0) : mword 64) (ITYPE (mword_of_int 2828 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) rwb_b0c78793. Qed.

  Lemma rwi_1c4 : kernel_text -∗ instr (mword_of_int (VRW + 0x1c4) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (VRW + 0x1c4)%Z (mword_of_int 0x97ba : mword 16)
    (mword_of_int (VRW + 0x1c4) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97ba exec_execute_C_ADD. Qed.

  Lemma rwi_1c6 : kernel_text -∗ instr (mword_of_int (VRW + 0x1c6) : mword 64) false (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 8)).
  Proof. mk_base (VRW + 0x1c6)%Z (mword_of_int 0x0007b423 : mword 32)
    (mword_of_int (VRW + 0x1c6) : mword 64) (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 8)) rwb_0007b423. Qed.

  Lemma rwi_1ca : kernel_text -∗ instr (mword_of_int (VRW + 0x1ca) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 19), AUIPC)).
  Proof. mk_base (VRW + 0x1ca)%Z (mword_of_int 0x0001e997 : mword 32)
    (mword_of_int (VRW + 0x1ca) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 19), AUIPC)) rwb_0001e997. Qed.

  Lemma rwi_1ce : kernel_text -∗ instr (mword_of_int (VRW + 0x1ce) : mword 64) false (ITYPE (mword_of_int 2814 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI)).
  Proof. mk_base (VRW + 0x1ce)%Z (mword_of_int 0xafe98993 : mword 32)
    (mword_of_int (VRW + 0x1ce) : mword 64) (ITYPE (mword_of_int 2814 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI)) rwb_afe98993. Qed.

  Lemma rwi_1d2 : kernel_text -∗ instr (mword_of_int (VRW + 0x1d2) : mword 64) false (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 18), Regidx (mword_of_int 14), SLLI)).
  Proof. mk_base (VRW + 0x1d2)%Z (mword_of_int 0x00491713 : mword 32)
    (mword_of_int (VRW + 0x1d2) : mword 64) (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 18), Regidx (mword_of_int 14), SLLI)) rwb_00491713. Qed.

  Lemma rwi_1d6 : kernel_text -∗ instr (mword_of_int (VRW + 0x1d6) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (VRW + 0x1d6)%Z (mword_of_int 0x0009b783 : mword 32)
    (mword_of_int (VRW + 0x1d6) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), false, 8)) rwb_0009b783. Qed.

  Lemma rwi_1da : kernel_text -∗ instr (mword_of_int (VRW + 0x1da) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (VRW + 0x1da)%Z (mword_of_int 0x97ba : mword 16)
    (mword_of_int (VRW + 0x1da) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97ba exec_execute_C_ADD. Qed.

  Lemma rwi_1dc : kernel_text -∗ instr (mword_of_int (VRW + 0x1dc) : mword 64) false (LOAD (mword_of_int 12 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), true, 2)).
  Proof. mk_base (VRW + 0x1dc)%Z (mword_of_int 0x00c7d483 : mword 32)
    (mword_of_int (VRW + 0x1dc) : mword 64) (LOAD (mword_of_int 12 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), true, 2)) rwb_00c7d483. Qed.

  Lemma rwi_1e0 : kernel_text -∗ instr (mword_of_int (VRW + 0x1e0) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (VRW + 0x1e0)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (VRW + 0x1e0) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  Lemma rwi_1e2 : kernel_text -∗ instr (mword_of_int (VRW + 0x1e2) : mword 64) false (LOAD (mword_of_int 14 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 18), true, 2)).
  Proof. mk_base (VRW + 0x1e2)%Z (mword_of_int 0x00e7d903 : mword 32)
    (mword_of_int (VRW + 0x1e2) : mword 64) (LOAD (mword_of_int 14 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 18), true, 2)) rwb_00e7d903. Qed.

  Lemma rwi_1e6 : kernel_text -∗ instr (mword_of_int (VRW + 0x1e6) : mword 64) false (JAL (mword_of_int 2096092 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VRW + 0x1e6)%Z (mword_of_int 0xbddff0ef : mword 32)
    (mword_of_int (VRW + 0x1e6) : mword 64) (JAL (mword_of_int 2096092 : mword 21, Regidx (mword_of_int 1))) rwb_bddff0ef. Qed.

  Lemma rwi_1ea : kernel_text -∗ instr (mword_of_int (VRW + 0x1ea) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ANDI)).
  Proof. mk_rvc (VRW + 0x1ea)%Z (mword_of_int 0x8885 : mword 16)
    (mword_of_int (VRW + 0x1ea) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ANDI)) rwc_8885 rwe_8885. Qed.

  Lemma rwi_1ec : kernel_text -∗ instr (mword_of_int (VRW + 0x1ec) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 243 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BNE)).
  Proof. mk_rvc (VRW + 0x1ec)%Z (mword_of_int 0xf0fd : mword 16)
    (mword_of_int (VRW + 0x1ec) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 243 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BNE)) rwc_f0fd exec_execute_C_BNEZ. Qed.

  Lemma rwi_1ee : kernel_text -∗ instr (mword_of_int (VRW + 0x1ee) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (VRW + 0x1ee)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (VRW + 0x1ee) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  Lemma rwi_1f2 : kernel_text -∗ instr (mword_of_int (VRW + 0x1f2) : mword 64) false (ITYPE (mword_of_int 3074 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (VRW + 0x1f2)%Z (mword_of_int 0xc0250513 : mword 32)
    (mword_of_int (VRW + 0x1f2) : mword 64) (ITYPE (mword_of_int 3074 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) rwb_c0250513. Qed.

  Lemma rwi_1f6 : kernel_text -∗ instr (mword_of_int (VRW + 0x1f6) : mword 64) false (JAL (mword_of_int 2077514 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VRW + 0x1f6)%Z (mword_of_int 0xb4afb0ef : mword 32)
    (mword_of_int (VRW + 0x1f6) : mword 64) (JAL (mword_of_int 2077514 : mword 21, Regidx (mword_of_int 1))) rwb_b4afb0ef. Qed.

  Lemma rwi_1fa : kernel_text -∗ instr (mword_of_int (VRW + 0x1fa) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (VRW + 0x1fa)%Z (mword_of_int 0x60e6 : mword 16)
    (mword_of_int (VRW + 0x1fa) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e6 exec_execute_C_LDSP. Qed.

  Lemma rwi_1fc : kernel_text -∗ instr (mword_of_int (VRW + 0x1fc) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (VRW + 0x1fc)%Z (mword_of_int 0x6446 : mword 16)
    (mword_of_int (VRW + 0x1fc) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6446 exec_execute_C_LDSP. Qed.

  Lemma rwi_1fe : kernel_text -∗ instr (mword_of_int (VRW + 0x1fe) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (VRW + 0x1fe)%Z (mword_of_int 0x64a6 : mword 16)
    (mword_of_int (VRW + 0x1fe) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a6 exec_execute_C_LDSP. Qed.

  Lemma rwi_200 : kernel_text -∗ instr (mword_of_int (VRW + 0x200) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (VRW + 0x200)%Z (mword_of_int 0x6906 : mword 16)
    (mword_of_int (VRW + 0x200) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6906 exec_execute_C_LDSP. Qed.

  Lemma rwi_202 : kernel_text -∗ instr (mword_of_int (VRW + 0x202) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (VRW + 0x202)%Z (mword_of_int 0x79e2 : mword 16)
    (mword_of_int (VRW + 0x202) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_79e2 exec_execute_C_LDSP. Qed.

  Lemma rwi_204 : kernel_text -∗ instr (mword_of_int (VRW + 0x204) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (VRW + 0x204)%Z (mword_of_int 0x7a42 : mword 16)
    (mword_of_int (VRW + 0x204) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_7a42 exec_execute_C_LDSP. Qed.

  Lemma rwi_206 : kernel_text -∗ instr (mword_of_int (VRW + 0x206) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (VRW + 0x206)%Z (mword_of_int 0x7aa2 : mword 16)
    (mword_of_int (VRW + 0x206) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) cdec_7aa2 exec_execute_C_LDSP. Qed.

  Lemma rwi_208 : kernel_text -∗ instr (mword_of_int (VRW + 0x208) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (VRW + 0x208)%Z (mword_of_int 0x7b02 : mword 16)
    (mword_of_int (VRW + 0x208) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) cdec_7b02 exec_execute_C_LDSP. Qed.

  Lemma rwi_20a : kernel_text -∗ instr (mword_of_int (VRW + 0x20a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).
  Proof. mk_rvc (VRW + 0x20a)%Z (mword_of_int 0x6be2 : mword 16)
    (mword_of_int (VRW + 0x20a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) cdec_6be2 exec_execute_C_LDSP. Qed.

  Lemma rwi_20c : kernel_text -∗ instr (mword_of_int (VRW + 0x20c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)).
  Proof. mk_rvc (VRW + 0x20c)%Z (mword_of_int 0x6c42 : mword 16)
    (mword_of_int (VRW + 0x20c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)) cdec_6c42 exec_execute_C_LDSP. Qed.

  Lemma rwi_20e : kernel_text -∗ instr (mword_of_int (VRW + 0x20e) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 6 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (VRW + 0x20e)%Z (mword_of_int 0x6125 : mword 16)
    (mword_of_int (VRW + 0x20e) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 6 : mword 6), sp, sp, ADDI)) cdec_6125 exec_execute_C_ADDI16SP. Qed.

  Lemma rwi_210 : kernel_text -∗ instr (mword_of_int (VRW + 0x210) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (VRW + 0x210)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (VRW + 0x210) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.


End VirtioDiskRwInstrs.
