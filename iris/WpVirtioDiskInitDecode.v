(* WpVirtioDiskInitDecode.v -- the instruction-DECODE layer for xv6's
   virtio_disk_init().  For every instruction of

     virtio_disk_init @ 0x80005588 .. 0x80005706   (offsets 0x000 .. 0x17e)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([vdi_<off>]) plus
   the per-instruction decode facts they consume ([vdc_<word>] compressed /
   [vdb_<word>] base) and, where the RVC expansion needs bridging to the WP
   leaves' shape (a literal [mword 12] offset and plain [Regidx]es rather than
   [zero_extend' 12 (concat_vec uimm _)] / [creg2reg_idx]), the leaf-form
   expansion [vde_<word>].

   The instruction bytes come from the TRACKED [Kernel.KernelInstrs] image, via
   [mk_rvc]/[mk_base]; the six panic tails at 0x80005708.. are NOT decoded --
   every branch to them is refuted in ProofVirtioDiskInit.v.

   The standard 4-slot frame words and the shared c.li/c.lui/c.addiw/c.ret
   templates come from KernelRvcDecode.v; the auipc a0,0x1e word from
   KernelBaseDecode.v.  Everything else carries virtio_disk_init's own
   encodings and is proved here. *)
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
(* creg -> reg bridges for the three compressed register fields whose      *)
(* expansions are not covered by a [_leaf] lemma (c.and, c.srai).          *)
(* ===================================================================== *)
Lemma vdi_cr5 : creg2reg_idx (Cregidx (mword_of_int 5)) = Regidx (mword_of_int 13).
Proof. vm_compute. reflexivity. Qed.
Lemma vdi_cr6 : creg2reg_idx (Cregidx (mword_of_int 6)) = Regidx (mword_of_int 14).
Proof. vm_compute. reflexivity. Qed.
Lemma vdi_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx (mword_of_int 15).
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(* Compressed decode facts unique to virtio_disk_init.                    *)
(* ===================================================================== *)

Lemma vdc_4398 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4398 : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_2701 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2701 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 0, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_43dc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x43dc : mword 16)) s
  = Some (C_LW (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_4709 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4709 : mword 16)) s
  = Some (C_LI (mword_of_int 2, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_479c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x479c : mword 16)) s
  = Some (C_LW (mword_of_int 2, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_47d8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x47d8 : mword 16)) s
  = Some (C_LW (mword_of_int 3, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_4705 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4705 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_dbb8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xdbb8 : mword 16)) s
  = Some (C_SW (mword_of_int 28, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_470d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x470d : mword 16)) s
  = Some (C_LI (mword_of_int 3, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_4b18 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4b18 : mword 16)) s
  = Some (C_LW (mword_of_int 4, Cregidx (mword_of_int 6), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_8f75 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8f75 : mword 16)) s
  = Some (C_AND (Cregidx (mword_of_int 6), Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_d298 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd298 : mword 16)) s
  = Some (C_SW (mword_of_int 8, Cregidx (mword_of_int 5), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_472d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x472d : mword 16)) s
  = Some (C_LI (mword_of_int 11, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_439c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x439c : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_8ba1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8ba1 : mword 16)) s
  = Some (C_ANDI (mword_of_int 8, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_43fc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x43fc : mword 16)) s
  = Some (C_LW (mword_of_int 17, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_5bdc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x5bdc : mword 16)) s
  = Some (C_LW (mword_of_int 13, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_471d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x471d : mword 16)) s
  = Some (C_LI (mword_of_int 7, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_e088 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe088 : mword 16)) s
  = Some (C_SD (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_e488 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe488 : mword 16)) s
  = Some (C_SD (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_87aa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x87aa : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_e888 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe888 : mword 16)) s
  = Some (C_SD (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_6088 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6088 : mword 16)) s
  = Some (C_LD (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_cb71 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcb71 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 106, Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_cbe9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcbe9 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 105, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_6488 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6488 : mword 16)) s
  = Some (C_LD (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_6888 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6888 : mword 16)) s
  = Some (C_LD (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_4721 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4721 : mword 16)) s
  = Some (C_LI (mword_of_int 8, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_df98 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xdf98 : mword 16)) s
  = Some (C_SW (mword_of_int 14, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_4098 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4098 : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_40d8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x40d8 : mword 16)) s
  = Some (C_LW (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_649c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x649c : mword 16)) s
  = Some (C_LD (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_9781 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9781 : mword 16)) s
  = Some (C_SRAI (mword_of_int 32, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_689c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x689c : mword 16)) s
  = Some (C_LD (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma vdc_c37c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc37c : mword 16)) s
  = Some (C_SW (mword_of_int 17, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Leaf-form RVC expansions (WpMmodeLeafBase's [_leaf] bridges at this      *)
(* function's concrete operands), plus c.and / c.andi / c.srai.            *)
(* ===================================================================== *)

Lemma vde_4398 s :
  exec (execute (C_LW (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_43dc s :
  exec (execute (C_LW (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_479c s :
  exec (execute (C_LW (mword_of_int 2, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 8, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_47d8 s :
  exec (execute (C_LW (mword_of_int 3, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_4b18 s :
  exec (execute (C_LW (mword_of_int 4, Cregidx (mword_of_int 6), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 16, Regidx (mword_of_int 14), Regidx (mword_of_int 14), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_439c s :
  exec (execute (C_LW (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_43fc s :
  exec (execute (C_LW (mword_of_int 17, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 68, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_5bdc s :
  exec (execute (C_LW (mword_of_int 13, Cregidx (mword_of_int 7), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 52, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_4098 s :
  exec (execute (C_LW (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_40d8 s :
  exec (execute (C_LW (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_dbb8 s :
  exec (execute (C_SW (mword_of_int 28, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (STORE (mword_of_int 112, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_d298 s :
  exec (execute (C_SW (mword_of_int 8, Cregidx (mword_of_int 5), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (STORE (mword_of_int 32, Regidx (mword_of_int 14), Regidx (mword_of_int 13), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_df98 s :
  exec (execute (C_SW (mword_of_int 14, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (STORE (mword_of_int 56, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_c37c s :
  exec (execute (C_SW (mword_of_int 17, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 68, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_6088 s :
  exec (execute (C_LD (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_6488 s :
  exec (execute (C_LD (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 8, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_6888 s :
  exec (execute (C_LD (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_649c s :
  exec (execute (C_LD (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 8, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_689c s :
  exec (execute (C_LD (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_e088 s :
  exec (execute (C_SD (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (STORE (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_e488 s :
  exec (execute (C_SD (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (STORE (mword_of_int 8, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_e888 s :
  exec (execute (C_SD (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (STORE (mword_of_int 16, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma vde_8f75 s :
  exec (execute (C_AND (Cregidx (mword_of_int 6), Cregidx (mword_of_int 5)))) s
  = Some (ExecuteAs (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 14), Regidx (mword_of_int 14), AND)), s).
Proof. rewrite exec_execute_C_AND vdi_cr5 vdi_cr6. reflexivity. Qed.

Lemma vde_8ba1 s :
  exec (execute (C_ANDI (mword_of_int 8, Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)), s).
Proof. apply exec_execute_C_ANDI_leaf. vm_compute. reflexivity. Qed.

Lemma vde_9781 s :
  exec (execute (C_SRAI (mword_of_int 32, Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SRAI)), s).
Proof. rewrite exec_execute_C_SRAI vdi_cr7. reflexivity. Qed.

(* ===================================================================== *)
(* Base (32-bit) decode facts unique to virtio_disk_init.  Negative addi   *)
(* immediates appear as the decoder's POSITIVE RESIDUE (-92 -> 4004, ...). *)
(* ===================================================================== *)

Lemma vdb_00002597 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00002597 : mword 32)) s
  = Some (UTYPE (mword_of_int 2 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_09c58593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x09c58593 : mword 32)) s
  = Some (ITYPE (mword_of_int 156 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_fa450513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfa450513 : mword 32)) s
  = Some (ITYPE (mword_of_int 4004 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_de4fb0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xde4fb0ef : mword 32)) s
  = Some (JAL (mword_of_int 2078180 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_100017b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x100017b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_747277b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x747277b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 476967 : mword 20, Regidx (mword_of_int 15), LUI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_97678793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x97678793 : mword 32)) s
  = Some (ITYPE (mword_of_int 2422 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_14f71863 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x14f71863 : mword 32)) s
  = Some (BTYPE (mword_of_int 336 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_14e79163 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x14e79163 : mword 32)) s
  = Some (BTYPE (mword_of_int 322 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_12e79b63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x12e79b63 : mword 32)) s
  = Some (BTYPE (mword_of_int 310 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_554d47b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x554d47b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 349396 : mword 20, Regidx (mword_of_int 15), LUI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_55178793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x55178793 : mword 32)) s
  = Some (ITYPE (mword_of_int 1361 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_12f71163 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x12f71163 : mword 32)) s
  = Some (BTYPE (mword_of_int 290 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_0607a823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0607a823 : mword 32)) s
  = Some (STORE (mword_of_int 112 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_10001737 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x10001737 : mword 32)) s
  = Some (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 14), LUI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_c7ffe6b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc7ffe6b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 819198 : mword 20, Regidx (mword_of_int 13), LUI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_75f68693 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x75f68693 : mword 32)) s
  = Some (ITYPE (mword_of_int 1887 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_100016b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x100016b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 13), LUI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_07078793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x07078793 : mword 32)) s
  = Some (ITYPE (mword_of_int 112 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_0007891b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007891b : mword 32)) s
  = Some (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 18)), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_0e078a63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0e078a63 : mword 32)) s
  = Some (BTYPE (mword_of_int 244 : mword 13, zreg, Regidx (mword_of_int 15), BEQ), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_0207a823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0207a823 : mword 32)) s
  = Some (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_0e079863 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0e079863 : mword 32)) s
  = Some (BTYPE (mword_of_int 240 : mword 13, zreg, Regidx (mword_of_int 15), BNE), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_0e078863 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0e078863 : mword 32)) s
  = Some (BTYPE (mword_of_int 240 : mword 13, zreg, Regidx (mword_of_int 15), BEQ), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_0ef77b63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0ef77b63 : mword 32)) s
  = Some (BTYPE (mword_of_int 246 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BGEU), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_ce8fb0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xce8fb0ef : mword 32)) s
  = Some (JAL (mword_of_int 2077928 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_0001e497 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e497 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_dce48493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xdce48493 : mword 32)) s
  = Some (ITYPE (mword_of_int 3534 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_cdafb0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xcdafb0ef : mword 32)) s
  = Some (JAL (mword_of_int 2077914 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_cd4fb0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xcd4fb0ef : mword 32)) s
  = Some (JAL (mword_of_int 2077908 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_0e050063 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0e050063 : mword 32)) s
  = Some (BTYPE (mword_of_int 224 : mword 13, zreg, Regidx (mword_of_int 10), BEQ), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_0001e717 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e717 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_db873703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xdb873703 : mword 32)) s
  = Some (LOAD (mword_of_int 3512 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), false, 8), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_e50fb0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe50fb0ef : mword 32)) s
  = Some (JAL (mword_of_int 2078288 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_d9c48493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd9c48493 : mword 32)) s
  = Some (ITYPE (mword_of_int 3484 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_e3efb0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe3efb0ef : mword 32)) s
  = Some (JAL (mword_of_int 2078270 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_e34fb0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe34fb0ef : mword 32)) s
  = Some (JAL (mword_of_int 2078260 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_08e7a023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x08e7a023 : mword 32)) s
  = Some (STORE (mword_of_int 128 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_08e7a223 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x08e7a223 : mword 32)) s
  = Some (STORE (mword_of_int 132 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_0007869b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007869b : mword 32)) s
  = Some (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13)), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_08d72823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x08d72823 : mword 32)) s
  = Some (STORE (mword_of_int 144 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_08f72a23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x08f72a23 : mword 32)) s
  = Some (STORE (mword_of_int 148 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_0ad72023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0ad72023 : mword 32)) s
  = Some (STORE (mword_of_int 160 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_0af72223 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0af72223 : mword 32)) s
  = Some (STORE (mword_of_int 164 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_00f48c23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f48c23 : mword 32)) s
  = Some (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_00f48ca3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f48ca3 : mword 32)) s
  = Some (STORE (mword_of_int 25 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_00f48d23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f48d23 : mword 32)) s
  = Some (STORE (mword_of_int 26 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_00f48da3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f48da3 : mword 32)) s
  = Some (STORE (mword_of_int 27 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_00f48e23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f48e23 : mword 32)) s
  = Some (STORE (mword_of_int 28 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_00f48ea3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f48ea3 : mword 32)) s
  = Some (STORE (mword_of_int 29 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_00f48f23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f48f23 : mword 32)) s
  = Some (STORE (mword_of_int 30 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_00f48fa3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f48fa3 : mword 32)) s
  = Some (STORE (mword_of_int 31 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_00496913 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00496913 : mword 32)) s
  = Some (ITYPE (mword_of_int 4 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ORI), s).
Proof. decode_bridge_ms. Qed.

Lemma vdb_07272823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x07272823 : mword 32)) s
  = Some (STORE (mword_of_int 112 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 14), 4), s).
Proof. decode_bridge_ms. Qed.
(* ===================================================================== *)
(* The per-instruction [instr] facts, entry (+0x000) through ret (+0x17e). *)
(* ===================================================================== *)
Section WpVirtioDiskInitDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation VDI := KernelSyms.virtio_disk_init.

  Lemma vdi_000 : kernel_text -∗ instr (mword_of_int VDI : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc VDI (mword_of_int 0x1101 : mword 16)
    (mword_of_int VDI : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma vdi_002 : kernel_text -∗ instr (mword_of_int (VDI + 0x002) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (VDI + 0x002)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (VDI + 0x002) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma vdi_004 : kernel_text -∗ instr (mword_of_int (VDI + 0x004) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (VDI + 0x004)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (VDI + 0x004) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma vdi_006 : kernel_text -∗ instr (mword_of_int (VDI + 0x006) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (VDI + 0x006)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (VDI + 0x006) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma vdi_008 : kernel_text -∗ instr (mword_of_int (VDI + 0x008) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (VDI + 0x008)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (VDI + 0x008) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  Lemma vdi_00a : kernel_text -∗ instr (mword_of_int (VDI + 0x00a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (VDI + 0x00a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (VDI + 0x00a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma vdi_00c : kernel_text -∗ instr (mword_of_int (VDI + 0x00c) : mword 64) false (UTYPE (mword_of_int 2 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (VDI + 0x00c)%Z (mword_of_int 0x00002597 : mword 32)
    (mword_of_int (VDI + 0x00c) : mword 64) (UTYPE (mword_of_int 2 : mword 20, Regidx (mword_of_int 11), AUIPC)) vdb_00002597. Qed.

  Lemma vdi_010 : kernel_text -∗ instr (mword_of_int (VDI + 0x010) : mword 64) false (ITYPE (mword_of_int 156 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (VDI + 0x010)%Z (mword_of_int 0x09c58593 : mword 32)
    (mword_of_int (VDI + 0x010) : mword 64) (ITYPE (mword_of_int 156 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) vdb_09c58593. Qed.

  Lemma vdi_014 : kernel_text -∗ instr (mword_of_int (VDI + 0x014) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (VDI + 0x014)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (VDI + 0x014) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  Lemma vdi_018 : kernel_text -∗ instr (mword_of_int (VDI + 0x018) : mword 64) false (ITYPE (mword_of_int 4004 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (VDI + 0x018)%Z (mword_of_int 0xfa450513 : mword 32)
    (mword_of_int (VDI + 0x018) : mword 64) (ITYPE (mword_of_int 4004 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) vdb_fa450513. Qed.

  Lemma vdi_01c : kernel_text -∗ instr (mword_of_int (VDI + 0x01c) : mword 64) false (JAL (mword_of_int 2078180 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VDI + 0x01c)%Z (mword_of_int 0xde4fb0ef : mword 32)
    (mword_of_int (VDI + 0x01c) : mword 64) (JAL (mword_of_int 2078180 : mword 21, Regidx (mword_of_int 1))) vdb_de4fb0ef. Qed.

  Lemma vdi_020 : kernel_text -∗ instr (mword_of_int (VDI + 0x020) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (VDI + 0x020)%Z (mword_of_int 0x100017b7 : mword 32)
    (mword_of_int (VDI + 0x020) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)) vdb_100017b7. Qed.

  Lemma vdi_024 : kernel_text -∗ instr (mword_of_int (VDI + 0x024) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_rvc (VDI + 0x024)%Z (mword_of_int 0x4398 : mword 16)
    (mword_of_int (VDI + 0x024) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 4)) vdc_4398 vde_4398. Qed.

  Lemma vdi_026 : kernel_text -∗ instr (mword_of_int (VDI + 0x026) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14))).
  Proof. mk_rvc (VDI + 0x026)%Z (mword_of_int 0x2701 : mword 16)
    (mword_of_int (VDI + 0x026) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14))) vdc_2701 exec_execute_C_ADDIW. Qed.

  Lemma vdi_028 : kernel_text -∗ instr (mword_of_int (VDI + 0x028) : mword 64) false (UTYPE (mword_of_int 476967 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (VDI + 0x028)%Z (mword_of_int 0x747277b7 : mword 32)
    (mword_of_int (VDI + 0x028) : mword 64) (UTYPE (mword_of_int 476967 : mword 20, Regidx (mword_of_int 15), LUI)) vdb_747277b7. Qed.

  Lemma vdi_02c : kernel_text -∗ instr (mword_of_int (VDI + 0x02c) : mword 64) false (ITYPE (mword_of_int 2422 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (VDI + 0x02c)%Z (mword_of_int 0x97678793 : mword 32)
    (mword_of_int (VDI + 0x02c) : mword 64) (ITYPE (mword_of_int 2422 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) vdb_97678793. Qed.

  Lemma vdi_030 : kernel_text -∗ instr (mword_of_int (VDI + 0x030) : mword 64) false (BTYPE (mword_of_int 336 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE)).
  Proof. mk_base (VDI + 0x030)%Z (mword_of_int 0x14f71863 : mword 32)
    (mword_of_int (VDI + 0x030) : mword 64) (BTYPE (mword_of_int 336 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE)) vdb_14f71863. Qed.

  Lemma vdi_034 : kernel_text -∗ instr (mword_of_int (VDI + 0x034) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (VDI + 0x034)%Z (mword_of_int 0x100017b7 : mword 32)
    (mword_of_int (VDI + 0x034) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)) vdb_100017b7. Qed.

  Lemma vdi_038 : kernel_text -∗ instr (mword_of_int (VDI + 0x038) : mword 64) true (LOAD (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (VDI + 0x038)%Z (mword_of_int 0x43dc : mword 16)
    (mword_of_int (VDI + 0x038) : mword 64) (LOAD (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) vdc_43dc vde_43dc. Qed.

  Lemma vdi_03a : kernel_text -∗ instr (mword_of_int (VDI + 0x03a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (VDI + 0x03a)%Z (mword_of_int 0x2781 : mword 16)
    (mword_of_int (VDI + 0x03a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2781 exec_execute_C_ADDIW. Qed.

  Lemma vdi_03c : kernel_text -∗ instr (mword_of_int (VDI + 0x03c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (VDI + 0x03c)%Z (mword_of_int 0x4709 : mword 16)
    (mword_of_int (VDI + 0x03c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) vdc_4709 exec_execute_C_LI. Qed.

  Lemma vdi_03e : kernel_text -∗ instr (mword_of_int (VDI + 0x03e) : mword 64) false (BTYPE (mword_of_int 322 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (VDI + 0x03e)%Z (mword_of_int 0x14e79163 : mword 32)
    (mword_of_int (VDI + 0x03e) : mword 64) (BTYPE (mword_of_int 322 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE)) vdb_14e79163. Qed.

  Lemma vdi_042 : kernel_text -∗ instr (mword_of_int (VDI + 0x042) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (VDI + 0x042)%Z (mword_of_int 0x100017b7 : mword 32)
    (mword_of_int (VDI + 0x042) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)) vdb_100017b7. Qed.

  Lemma vdi_046 : kernel_text -∗ instr (mword_of_int (VDI + 0x046) : mword 64) true (LOAD (mword_of_int 8, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (VDI + 0x046)%Z (mword_of_int 0x479c : mword 16)
    (mword_of_int (VDI + 0x046) : mword 64) (LOAD (mword_of_int 8, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) vdc_479c vde_479c. Qed.

  Lemma vdi_048 : kernel_text -∗ instr (mword_of_int (VDI + 0x048) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (VDI + 0x048)%Z (mword_of_int 0x2781 : mword 16)
    (mword_of_int (VDI + 0x048) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2781 exec_execute_C_ADDIW. Qed.

  Lemma vdi_04a : kernel_text -∗ instr (mword_of_int (VDI + 0x04a) : mword 64) false (BTYPE (mword_of_int 310 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (VDI + 0x04a)%Z (mword_of_int 0x12e79b63 : mword 32)
    (mword_of_int (VDI + 0x04a) : mword 64) (BTYPE (mword_of_int 310 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE)) vdb_12e79b63. Qed.

  Lemma vdi_04e : kernel_text -∗ instr (mword_of_int (VDI + 0x04e) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (VDI + 0x04e)%Z (mword_of_int 0x100017b7 : mword 32)
    (mword_of_int (VDI + 0x04e) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)) vdb_100017b7. Qed.

  Lemma vdi_052 : kernel_text -∗ instr (mword_of_int (VDI + 0x052) : mword 64) true (LOAD (mword_of_int 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_rvc (VDI + 0x052)%Z (mword_of_int 0x47d8 : mword 16)
    (mword_of_int (VDI + 0x052) : mword 64) (LOAD (mword_of_int 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 4)) vdc_47d8 vde_47d8. Qed.

  Lemma vdi_054 : kernel_text -∗ instr (mword_of_int (VDI + 0x054) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14))).
  Proof. mk_rvc (VDI + 0x054)%Z (mword_of_int 0x2701 : mword 16)
    (mword_of_int (VDI + 0x054) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14))) vdc_2701 exec_execute_C_ADDIW. Qed.

  Lemma vdi_056 : kernel_text -∗ instr (mword_of_int (VDI + 0x056) : mword 64) false (UTYPE (mword_of_int 349396 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (VDI + 0x056)%Z (mword_of_int 0x554d47b7 : mword 32)
    (mword_of_int (VDI + 0x056) : mword 64) (UTYPE (mword_of_int 349396 : mword 20, Regidx (mword_of_int 15), LUI)) vdb_554d47b7. Qed.

  Lemma vdi_05a : kernel_text -∗ instr (mword_of_int (VDI + 0x05a) : mword 64) false (ITYPE (mword_of_int 1361 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (VDI + 0x05a)%Z (mword_of_int 0x55178793 : mword 32)
    (mword_of_int (VDI + 0x05a) : mword 64) (ITYPE (mword_of_int 1361 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) vdb_55178793. Qed.

  Lemma vdi_05e : kernel_text -∗ instr (mword_of_int (VDI + 0x05e) : mword 64) false (BTYPE (mword_of_int 290 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE)).
  Proof. mk_base (VDI + 0x05e)%Z (mword_of_int 0x12f71163 : mword 32)
    (mword_of_int (VDI + 0x05e) : mword 64) (BTYPE (mword_of_int 290 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE)) vdb_12f71163. Qed.

  Lemma vdi_062 : kernel_text -∗ instr (mword_of_int (VDI + 0x062) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (VDI + 0x062)%Z (mword_of_int 0x100017b7 : mword 32)
    (mword_of_int (VDI + 0x062) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)) vdb_100017b7. Qed.

  Lemma vdi_066 : kernel_text -∗ instr (mword_of_int (VDI + 0x066) : mword 64) false (STORE (mword_of_int 112 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)).
  Proof. mk_base (VDI + 0x066)%Z (mword_of_int 0x0607a823 : mword 32)
    (mword_of_int (VDI + 0x066) : mword 64) (STORE (mword_of_int 112 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)) vdb_0607a823. Qed.

  Lemma vdi_06a : kernel_text -∗ instr (mword_of_int (VDI + 0x06a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (VDI + 0x06a)%Z (mword_of_int 0x4705 : mword 16)
    (mword_of_int (VDI + 0x06a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) vdc_4705 exec_execute_C_LI. Qed.

  Lemma vdi_06c : kernel_text -∗ instr (mword_of_int (VDI + 0x06c) : mword 64) true (STORE (mword_of_int 112, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)).
  Proof. mk_rvc (VDI + 0x06c)%Z (mword_of_int 0xdbb8 : mword 16)
    (mword_of_int (VDI + 0x06c) : mword 64) (STORE (mword_of_int 112, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)) vdc_dbb8 vde_dbb8. Qed.

  Lemma vdi_06e : kernel_text -∗ instr (mword_of_int (VDI + 0x06e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (VDI + 0x06e)%Z (mword_of_int 0x470d : mword 16)
    (mword_of_int (VDI + 0x06e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) vdc_470d exec_execute_C_LI. Qed.

  Lemma vdi_070 : kernel_text -∗ instr (mword_of_int (VDI + 0x070) : mword 64) true (STORE (mword_of_int 112, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)).
  Proof. mk_rvc (VDI + 0x070)%Z (mword_of_int 0xdbb8 : mword 16)
    (mword_of_int (VDI + 0x070) : mword 64) (STORE (mword_of_int 112, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)) vdc_dbb8 vde_dbb8. Qed.

  Lemma vdi_072 : kernel_text -∗ instr (mword_of_int (VDI + 0x072) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 14), LUI)).
  Proof. mk_base (VDI + 0x072)%Z (mword_of_int 0x10001737 : mword 32)
    (mword_of_int (VDI + 0x072) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 14), LUI)) vdb_10001737. Qed.

  Lemma vdi_076 : kernel_text -∗ instr (mword_of_int (VDI + 0x076) : mword 64) true (LOAD (mword_of_int 16, Regidx (mword_of_int 14), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_rvc (VDI + 0x076)%Z (mword_of_int 0x4b18 : mword 16)
    (mword_of_int (VDI + 0x076) : mword 64) (LOAD (mword_of_int 16, Regidx (mword_of_int 14), Regidx (mword_of_int 14), false, 4)) vdc_4b18 vde_4b18. Qed.

  Lemma vdi_078 : kernel_text -∗ instr (mword_of_int (VDI + 0x078) : mword 64) false (UTYPE (mword_of_int 819198 : mword 20, Regidx (mword_of_int 13), LUI)).
  Proof. mk_base (VDI + 0x078)%Z (mword_of_int 0xc7ffe6b7 : mword 32)
    (mword_of_int (VDI + 0x078) : mword 64) (UTYPE (mword_of_int 819198 : mword 20, Regidx (mword_of_int 13), LUI)) vdb_c7ffe6b7. Qed.

  Lemma vdi_07c : kernel_text -∗ instr (mword_of_int (VDI + 0x07c) : mword 64) false (ITYPE (mword_of_int 1887 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)).
  Proof. mk_base (VDI + 0x07c)%Z (mword_of_int 0x75f68693 : mword 32)
    (mword_of_int (VDI + 0x07c) : mword 64) (ITYPE (mword_of_int 1887 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)) vdb_75f68693. Qed.

  Lemma vdi_080 : kernel_text -∗ instr (mword_of_int (VDI + 0x080) : mword 64) true (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 14), Regidx (mword_of_int 14), AND)).
  Proof. mk_rvc (VDI + 0x080)%Z (mword_of_int 0x8f75 : mword 16)
    (mword_of_int (VDI + 0x080) : mword 64) (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 14), Regidx (mword_of_int 14), AND)) vdc_8f75 vde_8f75. Qed.

  Lemma vdi_082 : kernel_text -∗ instr (mword_of_int (VDI + 0x082) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 13), LUI)).
  Proof. mk_base (VDI + 0x082)%Z (mword_of_int 0x100016b7 : mword 32)
    (mword_of_int (VDI + 0x082) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 13), LUI)) vdb_100016b7. Qed.

  Lemma vdi_086 : kernel_text -∗ instr (mword_of_int (VDI + 0x086) : mword 64) true (STORE (mword_of_int 32, Regidx (mword_of_int 14), Regidx (mword_of_int 13), 4)).
  Proof. mk_rvc (VDI + 0x086)%Z (mword_of_int 0xd298 : mword 16)
    (mword_of_int (VDI + 0x086) : mword 64) (STORE (mword_of_int 32, Regidx (mword_of_int 14), Regidx (mword_of_int 13), 4)) vdc_d298 vde_d298. Qed.

  Lemma vdi_088 : kernel_text -∗ instr (mword_of_int (VDI + 0x088) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 11 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (VDI + 0x088)%Z (mword_of_int 0x472d : mword 16)
    (mword_of_int (VDI + 0x088) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 11 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) vdc_472d exec_execute_C_LI. Qed.

  Lemma vdi_08a : kernel_text -∗ instr (mword_of_int (VDI + 0x08a) : mword 64) true (STORE (mword_of_int 112, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)).
  Proof. mk_rvc (VDI + 0x08a)%Z (mword_of_int 0xdbb8 : mword 16)
    (mword_of_int (VDI + 0x08a) : mword 64) (STORE (mword_of_int 112, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)) vdc_dbb8 vde_dbb8. Qed.

  Lemma vdi_08c : kernel_text -∗ instr (mword_of_int (VDI + 0x08c) : mword 64) false (ITYPE (mword_of_int 112 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (VDI + 0x08c)%Z (mword_of_int 0x07078793 : mword 32)
    (mword_of_int (VDI + 0x08c) : mword 64) (ITYPE (mword_of_int 112 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) vdb_07078793. Qed.

  Lemma vdi_090 : kernel_text -∗ instr (mword_of_int (VDI + 0x090) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (VDI + 0x090)%Z (mword_of_int 0x439c : mword 16)
    (mword_of_int (VDI + 0x090) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) vdc_439c vde_439c. Qed.

  Lemma vdi_092 : kernel_text -∗ instr (mword_of_int (VDI + 0x092) : mword 64) false (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 18))).
  Proof. mk_base (VDI + 0x092)%Z (mword_of_int 0x0007891b : mword 32)
    (mword_of_int (VDI + 0x092) : mword 64) (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 18))) vdb_0007891b. Qed.

  Lemma vdi_096 : kernel_text -∗ instr (mword_of_int (VDI + 0x096) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_rvc (VDI + 0x096)%Z (mword_of_int 0x8ba1 : mword 16)
    (mword_of_int (VDI + 0x096) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) vdc_8ba1 vde_8ba1. Qed.

  Lemma vdi_098 : kernel_text -∗ instr (mword_of_int (VDI + 0x098) : mword 64) false (BTYPE (mword_of_int 244 : mword 13, zreg, Regidx (mword_of_int 15), BEQ)).
  Proof. mk_base (VDI + 0x098)%Z (mword_of_int 0x0e078a63 : mword 32)
    (mword_of_int (VDI + 0x098) : mword 64) (BTYPE (mword_of_int 244 : mword 13, zreg, Regidx (mword_of_int 15), BEQ)) vdb_0e078a63. Qed.

  Lemma vdi_09c : kernel_text -∗ instr (mword_of_int (VDI + 0x09c) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (VDI + 0x09c)%Z (mword_of_int 0x100017b7 : mword 32)
    (mword_of_int (VDI + 0x09c) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)) vdb_100017b7. Qed.

  Lemma vdi_0a0 : kernel_text -∗ instr (mword_of_int (VDI + 0x0a0) : mword 64) false (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)).
  Proof. mk_base (VDI + 0x0a0)%Z (mword_of_int 0x0207a823 : mword 32)
    (mword_of_int (VDI + 0x0a0) : mword 64) (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)) vdb_0207a823. Qed.

  Lemma vdi_0a4 : kernel_text -∗ instr (mword_of_int (VDI + 0x0a4) : mword 64) true (LOAD (mword_of_int 68, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (VDI + 0x0a4)%Z (mword_of_int 0x43fc : mword 16)
    (mword_of_int (VDI + 0x0a4) : mword 64) (LOAD (mword_of_int 68, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) vdc_43fc vde_43fc. Qed.

  Lemma vdi_0a6 : kernel_text -∗ instr (mword_of_int (VDI + 0x0a6) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (VDI + 0x0a6)%Z (mword_of_int 0x2781 : mword 16)
    (mword_of_int (VDI + 0x0a6) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2781 exec_execute_C_ADDIW. Qed.

  Lemma vdi_0a8 : kernel_text -∗ instr (mword_of_int (VDI + 0x0a8) : mword 64) false (BTYPE (mword_of_int 240 : mword 13, zreg, Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (VDI + 0x0a8)%Z (mword_of_int 0x0e079863 : mword 32)
    (mword_of_int (VDI + 0x0a8) : mword 64) (BTYPE (mword_of_int 240 : mword 13, zreg, Regidx (mword_of_int 15), BNE)) vdb_0e079863. Qed.

  Lemma vdi_0ac : kernel_text -∗ instr (mword_of_int (VDI + 0x0ac) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (VDI + 0x0ac)%Z (mword_of_int 0x100017b7 : mword 32)
    (mword_of_int (VDI + 0x0ac) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)) vdb_100017b7. Qed.

  Lemma vdi_0b0 : kernel_text -∗ instr (mword_of_int (VDI + 0x0b0) : mword 64) true (LOAD (mword_of_int 52, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (VDI + 0x0b0)%Z (mword_of_int 0x5bdc : mword 16)
    (mword_of_int (VDI + 0x0b0) : mword 64) (LOAD (mword_of_int 52, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) vdc_5bdc vde_5bdc. Qed.

  Lemma vdi_0b2 : kernel_text -∗ instr (mword_of_int (VDI + 0x0b2) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (VDI + 0x0b2)%Z (mword_of_int 0x2781 : mword 16)
    (mword_of_int (VDI + 0x0b2) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2781 exec_execute_C_ADDIW. Qed.

  Lemma vdi_0b4 : kernel_text -∗ instr (mword_of_int (VDI + 0x0b4) : mword 64) false (BTYPE (mword_of_int 240 : mword 13, zreg, Regidx (mword_of_int 15), BEQ)).
  Proof. mk_base (VDI + 0x0b4)%Z (mword_of_int 0x0e078863 : mword 32)
    (mword_of_int (VDI + 0x0b4) : mword 64) (BTYPE (mword_of_int 240 : mword 13, zreg, Regidx (mword_of_int 15), BEQ)) vdb_0e078863. Qed.

  Lemma vdi_0b8 : kernel_text -∗ instr (mword_of_int (VDI + 0x0b8) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 7 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (VDI + 0x0b8)%Z (mword_of_int 0x471d : mword 16)
    (mword_of_int (VDI + 0x0b8) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 7 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) vdc_471d exec_execute_C_LI. Qed.

  Lemma vdi_0ba : kernel_text -∗ instr (mword_of_int (VDI + 0x0ba) : mword 64) false (BTYPE (mword_of_int 246 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BGEU)).
  Proof. mk_base (VDI + 0x0ba)%Z (mword_of_int 0x0ef77b63 : mword 32)
    (mword_of_int (VDI + 0x0ba) : mword 64) (BTYPE (mword_of_int 246 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BGEU)) vdb_0ef77b63. Qed.

  Lemma vdi_0be : kernel_text -∗ instr (mword_of_int (VDI + 0x0be) : mword 64) false (JAL (mword_of_int 2077928 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VDI + 0x0be)%Z (mword_of_int 0xce8fb0ef : mword 32)
    (mword_of_int (VDI + 0x0be) : mword 64) (JAL (mword_of_int 2077928 : mword 21, Regidx (mword_of_int 1))) vdb_ce8fb0ef. Qed.

  Lemma vdi_0c2 : kernel_text -∗ instr (mword_of_int (VDI + 0x0c2) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (VDI + 0x0c2)%Z (mword_of_int 0x0001e497 : mword 32)
    (mword_of_int (VDI + 0x0c2) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)) vdb_0001e497. Qed.

  Lemma vdi_0c6 : kernel_text -∗ instr (mword_of_int (VDI + 0x0c6) : mword 64) false (ITYPE (mword_of_int 3534 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (VDI + 0x0c6)%Z (mword_of_int 0xdce48493 : mword 32)
    (mword_of_int (VDI + 0x0c6) : mword 64) (ITYPE (mword_of_int 3534 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) vdb_dce48493. Qed.

  Lemma vdi_0ca : kernel_text -∗ instr (mword_of_int (VDI + 0x0ca) : mword 64) true (STORE (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc (VDI + 0x0ca)%Z (mword_of_int 0xe088 : mword 16)
    (mword_of_int (VDI + 0x0ca) : mword 64) (STORE (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)) vdc_e088 vde_e088. Qed.

  Lemma vdi_0cc : kernel_text -∗ instr (mword_of_int (VDI + 0x0cc) : mword 64) false (JAL (mword_of_int 2077914 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VDI + 0x0cc)%Z (mword_of_int 0xcdafb0ef : mword 32)
    (mword_of_int (VDI + 0x0cc) : mword 64) (JAL (mword_of_int 2077914 : mword 21, Regidx (mword_of_int 1))) vdb_cdafb0ef. Qed.

  Lemma vdi_0d0 : kernel_text -∗ instr (mword_of_int (VDI + 0x0d0) : mword 64) true (STORE (mword_of_int 8, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc (VDI + 0x0d0)%Z (mword_of_int 0xe488 : mword 16)
    (mword_of_int (VDI + 0x0d0) : mword 64) (STORE (mword_of_int 8, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)) vdc_e488 vde_e488. Qed.

  Lemma vdi_0d2 : kernel_text -∗ instr (mword_of_int (VDI + 0x0d2) : mword 64) false (JAL (mword_of_int 2077908 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VDI + 0x0d2)%Z (mword_of_int 0xcd4fb0ef : mword 32)
    (mword_of_int (VDI + 0x0d2) : mword 64) (JAL (mword_of_int 2077908 : mword 21, Regidx (mword_of_int 1))) vdb_cd4fb0ef. Qed.

  Lemma vdi_0d6 : kernel_text -∗ instr (mword_of_int (VDI + 0x0d6) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (VDI + 0x0d6)%Z (mword_of_int 0x87aa : mword 16)
    (mword_of_int (VDI + 0x0d6) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 15), ADD)) vdc_87aa exec_execute_C_MV. Qed.

  Lemma vdi_0d8 : kernel_text -∗ instr (mword_of_int (VDI + 0x0d8) : mword 64) true (STORE (mword_of_int 16, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc (VDI + 0x0d8)%Z (mword_of_int 0xe888 : mword 16)
    (mword_of_int (VDI + 0x0d8) : mword 64) (STORE (mword_of_int 16, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)) vdc_e888 vde_e888. Qed.

  Lemma vdi_0da : kernel_text -∗ instr (mword_of_int (VDI + 0x0da) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_rvc (VDI + 0x0da)%Z (mword_of_int 0x6088 : mword 16)
    (mword_of_int (VDI + 0x0da) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)) vdc_6088 vde_6088. Qed.

  Lemma vdi_0dc : kernel_text -∗ instr (mword_of_int (VDI + 0x0dc) : mword 64) false (BTYPE (mword_of_int 224 : mword 13, zreg, Regidx (mword_of_int 10), BEQ)).
  Proof. mk_base (VDI + 0x0dc)%Z (mword_of_int 0x0e050063 : mword 32)
    (mword_of_int (VDI + 0x0dc) : mword 64) (BTYPE (mword_of_int 224 : mword 13, zreg, Regidx (mword_of_int 10), BEQ)) vdb_0e050063. Qed.

  Lemma vdi_0e0 : kernel_text -∗ instr (mword_of_int (VDI + 0x0e0) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (VDI + 0x0e0)%Z (mword_of_int 0x0001e717 : mword 32)
    (mword_of_int (VDI + 0x0e0) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)) vdb_0001e717. Qed.

  Lemma vdi_0e4 : kernel_text -∗ instr (mword_of_int (VDI + 0x0e4) : mword 64) false (LOAD (mword_of_int 3512 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), false, 8)).
  Proof. mk_base (VDI + 0x0e4)%Z (mword_of_int 0xdb873703 : mword 32)
    (mword_of_int (VDI + 0x0e4) : mword 64) (LOAD (mword_of_int 3512 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), false, 8)) vdb_db873703. Qed.

  Lemma vdi_0e8 : kernel_text -∗ instr (mword_of_int (VDI + 0x0e8) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 106 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BEQ)).
  Proof. mk_rvc (VDI + 0x0e8)%Z (mword_of_int 0xcb71 : mword 16)
    (mword_of_int (VDI + 0x0e8) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 106 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BEQ)) vdc_cb71 exec_execute_C_BEQZ. Qed.

  Lemma vdi_0ea : kernel_text -∗ instr (mword_of_int (VDI + 0x0ea) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 105 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (VDI + 0x0ea)%Z (mword_of_int 0xcbe9 : mword 16)
    (mword_of_int (VDI + 0x0ea) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 105 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) vdc_cbe9 exec_execute_C_BEQZ. Qed.

  Lemma vdi_0ec : kernel_text -∗ instr (mword_of_int (VDI + 0x0ec) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)).
  Proof. mk_rvc (VDI + 0x0ec)%Z (mword_of_int 0x6605 : mword 16)
    (mword_of_int (VDI + 0x0ec) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)) cdec_6605 exec_execute_C_LUI. Qed.

  Lemma vdi_0ee : kernel_text -∗ instr (mword_of_int (VDI + 0x0ee) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (VDI + 0x0ee)%Z (mword_of_int 0x4581 : mword 16)
    (mword_of_int (VDI + 0x0ee) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4581 exec_execute_C_LI. Qed.

  Lemma vdi_0f0 : kernel_text -∗ instr (mword_of_int (VDI + 0x0f0) : mword 64) false (JAL (mword_of_int 2078288 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VDI + 0x0f0)%Z (mword_of_int 0xe50fb0ef : mword 32)
    (mword_of_int (VDI + 0x0f0) : mword 64) (JAL (mword_of_int 2078288 : mword 21, Regidx (mword_of_int 1))) vdb_e50fb0ef. Qed.

  Lemma vdi_0f4 : kernel_text -∗ instr (mword_of_int (VDI + 0x0f4) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (VDI + 0x0f4)%Z (mword_of_int 0x0001e497 : mword 32)
    (mword_of_int (VDI + 0x0f4) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)) vdb_0001e497. Qed.

  Lemma vdi_0f8 : kernel_text -∗ instr (mword_of_int (VDI + 0x0f8) : mword 64) false (ITYPE (mword_of_int 3484 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (VDI + 0x0f8)%Z (mword_of_int 0xd9c48493 : mword 32)
    (mword_of_int (VDI + 0x0f8) : mword 64) (ITYPE (mword_of_int 3484 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) vdb_d9c48493. Qed.

  Lemma vdi_0fc : kernel_text -∗ instr (mword_of_int (VDI + 0x0fc) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)).
  Proof. mk_rvc (VDI + 0x0fc)%Z (mword_of_int 0x6605 : mword 16)
    (mword_of_int (VDI + 0x0fc) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)) cdec_6605 exec_execute_C_LUI. Qed.

  Lemma vdi_0fe : kernel_text -∗ instr (mword_of_int (VDI + 0x0fe) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (VDI + 0x0fe)%Z (mword_of_int 0x4581 : mword 16)
    (mword_of_int (VDI + 0x0fe) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4581 exec_execute_C_LI. Qed.

  Lemma vdi_100 : kernel_text -∗ instr (mword_of_int (VDI + 0x100) : mword 64) true (LOAD (mword_of_int 8, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_rvc (VDI + 0x100)%Z (mword_of_int 0x6488 : mword 16)
    (mword_of_int (VDI + 0x100) : mword 64) (LOAD (mword_of_int 8, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)) vdc_6488 vde_6488. Qed.

  Lemma vdi_102 : kernel_text -∗ instr (mword_of_int (VDI + 0x102) : mword 64) false (JAL (mword_of_int 2078270 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VDI + 0x102)%Z (mword_of_int 0xe3efb0ef : mword 32)
    (mword_of_int (VDI + 0x102) : mword 64) (JAL (mword_of_int 2078270 : mword 21, Regidx (mword_of_int 1))) vdb_e3efb0ef. Qed.

  Lemma vdi_106 : kernel_text -∗ instr (mword_of_int (VDI + 0x106) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)).
  Proof. mk_rvc (VDI + 0x106)%Z (mword_of_int 0x6605 : mword 16)
    (mword_of_int (VDI + 0x106) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)) cdec_6605 exec_execute_C_LUI. Qed.

  Lemma vdi_108 : kernel_text -∗ instr (mword_of_int (VDI + 0x108) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (VDI + 0x108)%Z (mword_of_int 0x4581 : mword 16)
    (mword_of_int (VDI + 0x108) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4581 exec_execute_C_LI. Qed.

  Lemma vdi_10a : kernel_text -∗ instr (mword_of_int (VDI + 0x10a) : mword 64) true (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_rvc (VDI + 0x10a)%Z (mword_of_int 0x6888 : mword 16)
    (mword_of_int (VDI + 0x10a) : mword 64) (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)) vdc_6888 vde_6888. Qed.

  Lemma vdi_10c : kernel_text -∗ instr (mword_of_int (VDI + 0x10c) : mword 64) false (JAL (mword_of_int 2078260 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VDI + 0x10c)%Z (mword_of_int 0xe34fb0ef : mword 32)
    (mword_of_int (VDI + 0x10c) : mword 64) (JAL (mword_of_int 2078260 : mword 21, Regidx (mword_of_int 1))) vdb_e34fb0ef. Qed.

  Lemma vdi_110 : kernel_text -∗ instr (mword_of_int (VDI + 0x110) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (VDI + 0x110)%Z (mword_of_int 0x100017b7 : mword 32)
    (mword_of_int (VDI + 0x110) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 15), LUI)) vdb_100017b7. Qed.

  Lemma vdi_114 : kernel_text -∗ instr (mword_of_int (VDI + 0x114) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (VDI + 0x114)%Z (mword_of_int 0x4721 : mword 16)
    (mword_of_int (VDI + 0x114) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) vdc_4721 exec_execute_C_LI. Qed.

  Lemma vdi_116 : kernel_text -∗ instr (mword_of_int (VDI + 0x116) : mword 64) true (STORE (mword_of_int 56, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)).
  Proof. mk_rvc (VDI + 0x116)%Z (mword_of_int 0xdf98 : mword 16)
    (mword_of_int (VDI + 0x116) : mword 64) (STORE (mword_of_int 56, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)) vdc_df98 vde_df98. Qed.

  Lemma vdi_118 : kernel_text -∗ instr (mword_of_int (VDI + 0x118) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_rvc (VDI + 0x118)%Z (mword_of_int 0x4098 : mword 16)
    (mword_of_int (VDI + 0x118) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)) vdc_4098 vde_4098. Qed.

  Lemma vdi_11a : kernel_text -∗ instr (mword_of_int (VDI + 0x11a) : mword 64) false (STORE (mword_of_int 128 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)).
  Proof. mk_base (VDI + 0x11a)%Z (mword_of_int 0x08e7a023 : mword 32)
    (mword_of_int (VDI + 0x11a) : mword 64) (STORE (mword_of_int 128 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)) vdb_08e7a023. Qed.

  Lemma vdi_11e : kernel_text -∗ instr (mword_of_int (VDI + 0x11e) : mword 64) true (LOAD (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_rvc (VDI + 0x11e)%Z (mword_of_int 0x40d8 : mword 16)
    (mword_of_int (VDI + 0x11e) : mword 64) (LOAD (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)) vdc_40d8 vde_40d8. Qed.

  Lemma vdi_120 : kernel_text -∗ instr (mword_of_int (VDI + 0x120) : mword 64) false (STORE (mword_of_int 132 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)).
  Proof. mk_base (VDI + 0x120)%Z (mword_of_int 0x08e7a223 : mword 32)
    (mword_of_int (VDI + 0x120) : mword 64) (STORE (mword_of_int 132 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)) vdb_08e7a223. Qed.

  Lemma vdi_124 : kernel_text -∗ instr (mword_of_int (VDI + 0x124) : mword 64) true (LOAD (mword_of_int 8, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc (VDI + 0x124)%Z (mword_of_int 0x649c : mword 16)
    (mword_of_int (VDI + 0x124) : mword 64) (LOAD (mword_of_int 8, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)) vdc_649c vde_649c. Qed.

  Lemma vdi_126 : kernel_text -∗ instr (mword_of_int (VDI + 0x126) : mword 64) false (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13))).
  Proof. mk_base (VDI + 0x126)%Z (mword_of_int 0x0007869b : mword 32)
    (mword_of_int (VDI + 0x126) : mword 64) (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13))) vdb_0007869b. Qed.

  Lemma vdi_12a : kernel_text -∗ instr (mword_of_int (VDI + 0x12a) : mword 64) false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 14), LUI)).
  Proof. mk_base (VDI + 0x12a)%Z (mword_of_int 0x10001737 : mword 32)
    (mword_of_int (VDI + 0x12a) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 14), LUI)) vdb_10001737. Qed.

  Lemma vdi_12e : kernel_text -∗ instr (mword_of_int (VDI + 0x12e) : mword 64) false (STORE (mword_of_int 144 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 4)).
  Proof. mk_base (VDI + 0x12e)%Z (mword_of_int 0x08d72823 : mword 32)
    (mword_of_int (VDI + 0x12e) : mword 64) (STORE (mword_of_int 144 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 4)) vdb_08d72823. Qed.

  Lemma vdi_132 : kernel_text -∗ instr (mword_of_int (VDI + 0x132) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SRAI)).
  Proof. mk_rvc (VDI + 0x132)%Z (mword_of_int 0x9781 : mword 16)
    (mword_of_int (VDI + 0x132) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SRAI)) vdc_9781 vde_9781. Qed.

  Lemma vdi_134 : kernel_text -∗ instr (mword_of_int (VDI + 0x134) : mword 64) false (STORE (mword_of_int 148 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)).
  Proof. mk_base (VDI + 0x134)%Z (mword_of_int 0x08f72a23 : mword 32)
    (mword_of_int (VDI + 0x134) : mword 64) (STORE (mword_of_int 148 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)) vdb_08f72a23. Qed.

  Lemma vdi_138 : kernel_text -∗ instr (mword_of_int (VDI + 0x138) : mword 64) true (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc (VDI + 0x138)%Z (mword_of_int 0x689c : mword 16)
    (mword_of_int (VDI + 0x138) : mword 64) (LOAD (mword_of_int 16, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)) vdc_689c vde_689c. Qed.

  Lemma vdi_13a : kernel_text -∗ instr (mword_of_int (VDI + 0x13a) : mword 64) false (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13))).
  Proof. mk_base (VDI + 0x13a)%Z (mword_of_int 0x0007869b : mword 32)
    (mword_of_int (VDI + 0x13a) : mword 64) (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13))) vdb_0007869b. Qed.

  Lemma vdi_13e : kernel_text -∗ instr (mword_of_int (VDI + 0x13e) : mword 64) false (STORE (mword_of_int 160 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 4)).
  Proof. mk_base (VDI + 0x13e)%Z (mword_of_int 0x0ad72023 : mword 32)
    (mword_of_int (VDI + 0x13e) : mword 64) (STORE (mword_of_int 160 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 4)) vdb_0ad72023. Qed.

  Lemma vdi_142 : kernel_text -∗ instr (mword_of_int (VDI + 0x142) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SRAI)).
  Proof. mk_rvc (VDI + 0x142)%Z (mword_of_int 0x9781 : mword 16)
    (mword_of_int (VDI + 0x142) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SRAI)) vdc_9781 vde_9781. Qed.

  Lemma vdi_144 : kernel_text -∗ instr (mword_of_int (VDI + 0x144) : mword 64) false (STORE (mword_of_int 164 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)).
  Proof. mk_base (VDI + 0x144)%Z (mword_of_int 0x0af72223 : mword 32)
    (mword_of_int (VDI + 0x144) : mword 64) (STORE (mword_of_int 164 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)) vdb_0af72223. Qed.

  Lemma vdi_148 : kernel_text -∗ instr (mword_of_int (VDI + 0x148) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (VDI + 0x148)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (VDI + 0x148) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.

  Lemma vdi_14a : kernel_text -∗ instr (mword_of_int (VDI + 0x14a) : mword 64) true (STORE (mword_of_int 68, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)).
  Proof. mk_rvc (VDI + 0x14a)%Z (mword_of_int 0xc37c : mword 16)
    (mword_of_int (VDI + 0x14a) : mword 64) (STORE (mword_of_int 68, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)) vdc_c37c vde_c37c. Qed.

  Lemma vdi_14c : kernel_text -∗ instr (mword_of_int (VDI + 0x14c) : mword 64) false (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)).
  Proof. mk_base (VDI + 0x14c)%Z (mword_of_int 0x00f48c23 : mword 32)
    (mword_of_int (VDI + 0x14c) : mword 64) (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)) vdb_00f48c23. Qed.

  Lemma vdi_150 : kernel_text -∗ instr (mword_of_int (VDI + 0x150) : mword 64) false (STORE (mword_of_int 25 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)).
  Proof. mk_base (VDI + 0x150)%Z (mword_of_int 0x00f48ca3 : mword 32)
    (mword_of_int (VDI + 0x150) : mword 64) (STORE (mword_of_int 25 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)) vdb_00f48ca3. Qed.

  Lemma vdi_154 : kernel_text -∗ instr (mword_of_int (VDI + 0x154) : mword 64) false (STORE (mword_of_int 26 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)).
  Proof. mk_base (VDI + 0x154)%Z (mword_of_int 0x00f48d23 : mword 32)
    (mword_of_int (VDI + 0x154) : mword 64) (STORE (mword_of_int 26 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)) vdb_00f48d23. Qed.

  Lemma vdi_158 : kernel_text -∗ instr (mword_of_int (VDI + 0x158) : mword 64) false (STORE (mword_of_int 27 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)).
  Proof. mk_base (VDI + 0x158)%Z (mword_of_int 0x00f48da3 : mword 32)
    (mword_of_int (VDI + 0x158) : mword 64) (STORE (mword_of_int 27 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)) vdb_00f48da3. Qed.

  Lemma vdi_15c : kernel_text -∗ instr (mword_of_int (VDI + 0x15c) : mword 64) false (STORE (mword_of_int 28 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)).
  Proof. mk_base (VDI + 0x15c)%Z (mword_of_int 0x00f48e23 : mword 32)
    (mword_of_int (VDI + 0x15c) : mword 64) (STORE (mword_of_int 28 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)) vdb_00f48e23. Qed.

  Lemma vdi_160 : kernel_text -∗ instr (mword_of_int (VDI + 0x160) : mword 64) false (STORE (mword_of_int 29 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)).
  Proof. mk_base (VDI + 0x160)%Z (mword_of_int 0x00f48ea3 : mword 32)
    (mword_of_int (VDI + 0x160) : mword 64) (STORE (mword_of_int 29 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)) vdb_00f48ea3. Qed.

  Lemma vdi_164 : kernel_text -∗ instr (mword_of_int (VDI + 0x164) : mword 64) false (STORE (mword_of_int 30 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)).
  Proof. mk_base (VDI + 0x164)%Z (mword_of_int 0x00f48f23 : mword 32)
    (mword_of_int (VDI + 0x164) : mword 64) (STORE (mword_of_int 30 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)) vdb_00f48f23. Qed.

  Lemma vdi_168 : kernel_text -∗ instr (mword_of_int (VDI + 0x168) : mword 64) false (STORE (mword_of_int 31 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)).
  Proof. mk_base (VDI + 0x168)%Z (mword_of_int 0x00f48fa3 : mword 32)
    (mword_of_int (VDI + 0x168) : mword 64) (STORE (mword_of_int 31 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 1)) vdb_00f48fa3. Qed.

  Lemma vdi_16c : kernel_text -∗ instr (mword_of_int (VDI + 0x16c) : mword 64) false (ITYPE (mword_of_int 4 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ORI)).
  Proof. mk_base (VDI + 0x16c)%Z (mword_of_int 0x00496913 : mword 32)
    (mword_of_int (VDI + 0x16c) : mword 64) (ITYPE (mword_of_int 4 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ORI)) vdb_00496913. Qed.

  Lemma vdi_170 : kernel_text -∗ instr (mword_of_int (VDI + 0x170) : mword 64) false (STORE (mword_of_int 112 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 14), 4)).
  Proof. mk_base (VDI + 0x170)%Z (mword_of_int 0x07272823 : mword 32)
    (mword_of_int (VDI + 0x170) : mword 64) (STORE (mword_of_int 112 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 14), 4)) vdb_07272823. Qed.

  Lemma vdi_174 : kernel_text -∗ instr (mword_of_int (VDI + 0x174) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (VDI + 0x174)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (VDI + 0x174) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma vdi_176 : kernel_text -∗ instr (mword_of_int (VDI + 0x176) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (VDI + 0x176)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (VDI + 0x176) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma vdi_178 : kernel_text -∗ instr (mword_of_int (VDI + 0x178) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (VDI + 0x178)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (VDI + 0x178) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma vdi_17a : kernel_text -∗ instr (mword_of_int (VDI + 0x17a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (VDI + 0x17a)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (VDI + 0x17a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  Lemma vdi_17c : kernel_text -∗ instr (mword_of_int (VDI + 0x17c) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (VDI + 0x17c)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (VDI + 0x17c) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma vdi_17e : kernel_text -∗ instr (mword_of_int (VDI + 0x17e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (VDI + 0x17e)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (VDI + 0x17e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End WpVirtioDiskInitDecode.