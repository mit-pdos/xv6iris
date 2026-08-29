(* UservecDefs.v -- shared uservec definitions: the 44-instruction catalog of
   the trap-entry half of the trampoline page (trampoline offsets 0x00..0x9b),
   in exactly the shape of UserretDefs.v -- words, ASTs, decode facts, and the
   [kernel_text]-backed [instr] constructors.  The va/pa windows ([uva]/[upa]),
   the register/creg helpers ([ureg]/[ucreg]) and the instruction forms shared
   with userret ([ai_sfence], [ai_lui], [ai_addiw], [ai_slli], [ai_ld]) come
   from UserretDefs. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecodeBridge WpRvcBridge.
Require Import WpGprCsrwB.
Require Import WpMmodeLeafBase.
Require Import KernelText.
Require Import UserretDefs.
From Kernel Require Import KernelInstrs.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 0. the one CSR number userret does not already name.                   *)
(* ===================================================================== *)

Definition csr_sscratch : mword 12 := mword_of_int 0x140.

(* ===================================================================== *)
(* 1. The uservec instruction words (trampoline + 0x00 .. 0x9b).          *)
(*                                                                        *)
(*    The [li a0,TRAMPOLINE] sequence at 0x04/0x08/0x0a is bit-identical  *)
(*    to userret's at 0xa8/0xac/0xae, and the two SFENCE.VMA at 0x8e/0x96 *)
(*    to userret's -- so those reuse UserretDefs' [uw_lui] / [uh_addiw] / *)
(*    [uh_slli] / [uw_sfence] and their decode facts.                     *)
(* ===================================================================== *)

Definition uvw_csrw_sscratch : mword 32 := mword_of_int 0x14051073.
Definition uvw_csrr_sscratch : mword 32 := mword_of_int 0x140022f3.
Definition uvw_csrw_satp     : mword 32 := mword_of_int 0x18031073.

(* --- the register-save stores, all a0-relative (a0 = TRAPFRAME) --- *)
Definition uvw_sd_ra  : mword 32 := mword_of_int 0x02153423.
Definition uvw_sd_sp  : mword 32 := mword_of_int 0x02253823.
Definition uvw_sd_gp  : mword 32 := mword_of_int 0x02353c23.
Definition uvw_sd_tp  : mword 32 := mword_of_int 0x04453023.
Definition uvw_sd_t0  : mword 32 := mword_of_int 0x04553423.
Definition uvw_sd_t1  : mword 32 := mword_of_int 0x04653823.
Definition uvw_sd_t2  : mword 32 := mword_of_int 0x04753c23.
Definition uvw_sd_a6  : mword 32 := mword_of_int 0x0b053023.
Definition uvw_sd_a7  : mword 32 := mword_of_int 0x0b153423.
Definition uvw_sd_s2  : mword 32 := mword_of_int 0x0b253823.
Definition uvw_sd_s3  : mword 32 := mword_of_int 0x0b353c23.
Definition uvw_sd_s4  : mword 32 := mword_of_int 0x0d453023.
Definition uvw_sd_s5  : mword 32 := mword_of_int 0x0d553423.
Definition uvw_sd_s6  : mword 32 := mword_of_int 0x0d653823.
Definition uvw_sd_s7  : mword 32 := mword_of_int 0x0d753c23.
Definition uvw_sd_s8  : mword 32 := mword_of_int 0x0f853023.
Definition uvw_sd_s9  : mword 32 := mword_of_int 0x0f953423.
Definition uvw_sd_s10 : mword 32 := mword_of_int 0x0fa53823.
Definition uvw_sd_s11 : mword 32 := mword_of_int 0x0fb53c23.
Definition uvw_sd_t3  : mword 32 := mword_of_int 0x11c53023.
Definition uvw_sd_t4  : mword 32 := mword_of_int 0x11d53423.
Definition uvw_sd_t5  : mword 32 := mword_of_int 0x11e53823.
Definition uvw_sd_t6  : mword 32 := mword_of_int 0x11f53c23.
(* the user's a0, recovered from sscratch into t0, into the a0 slot (112) *)
Definition uvw_sd_a0  : mword 32 := mword_of_int 0x06553823.

(* --- the four kernel-context loads out of the trapframe --- *)
Definition uvw_ld_sp : mword 32 := mword_of_int 0x00853103.
Definition uvw_ld_tp : mword 32 := mword_of_int 0x02053203.
Definition uvw_ld_t0 : mword 32 := mword_of_int 0x01053283.
Definition uvw_ld_t1 : mword 32 := mword_of_int 0x00053303.

(* --- compressed halves --- *)
Definition uvh_csd_s0 : mword 16 := mword_of_int 0xf120.
Definition uvh_csd_s1 : mword 16 := mword_of_int 0xf524.
Definition uvh_csd_a1 : mword 16 := mword_of_int 0xfd2c.
Definition uvh_csd_a2 : mword 16 := mword_of_int 0xe150.
Definition uvh_csd_a3 : mword 16 := mword_of_int 0xe554.
Definition uvh_csd_a4 : mword 16 := mword_of_int 0xe958.
Definition uvh_csd_a5 : mword 16 := mword_of_int 0xed5c.
Definition uvh_cjalr_t0 : mword 16 := mword_of_int 0x9282.

(* ===================================================================== *)
(* 2. The ASTs.                                                           *)
(* ===================================================================== *)

(* the a0-relative width-8 store; the mirror of UserretDefs' [ai_ld]. *)
Definition uvai_sd (rs2 : Z) (imm : Z) : instruction :=
  STORE (mword_of_int imm, ureg rs2, ureg 10, 8).

(* the expanded form of a compressed a0-relative sd of an x8..x15 source;
   the mirror of UserretDefs' [ai_cld_tgt]. *)
Definition uvai_csd_tgt (rs2c : Z) (uimm : Z) : instruction :=
  STORE (mword_of_int (uimm * 8), ureg (8 + rs2c), ureg 10, 8).

Definition uvai_csrw_sscratch : instruction :=
  CSRReg (csr_sscratch, ureg 10, zreg, CSRRW).
Definition uvai_csrr_sscratch : instruction :=
  CSRReg (csr_sscratch, zreg, ureg 5, CSRRS).
Definition uvai_csrw_satp : instruction :=
  CSRReg (csr_satp, ureg 6, zreg, CSRRW).
(* c.jalr t0 expands to [jalr ra, 0(t0)]. *)
Definition uvai_jalr_t0 : instruction := JALR (zeros' 12, ureg 5, ra).

(* the C_JALR execute expansion (the compressed forms userret needed all live
   in WpMmodeLeafBase; this one did not). *)

(* ===================================================================== *)
(* 3. Decode facts.                                                       *)
(* ===================================================================== *)

Lemma uvdec_csrw_sscratch s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_csrw_sscratch) s = Some (uvai_csrw_sscratch, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_csrr_sscratch s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_csrr_sscratch) s = Some (uvai_csrr_sscratch, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_csrw_satp s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_csrw_satp) s = Some (uvai_csrw_satp, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_ra s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_ra) s = Some (uvai_sd 1 40, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_sp s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_sp) s = Some (uvai_sd 2 48, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_gp s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_gp) s = Some (uvai_sd 3 56, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_tp s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_tp) s = Some (uvai_sd 4 64, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_t0 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_t0) s = Some (uvai_sd 5 72, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_t1 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_t1) s = Some (uvai_sd 6 80, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_t2 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_t2) s = Some (uvai_sd 7 88, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_a6 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_a6) s = Some (uvai_sd 16 160, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_a7 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_a7) s = Some (uvai_sd 17 168, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_s2 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_s2) s = Some (uvai_sd 18 176, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_s3 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_s3) s = Some (uvai_sd 19 184, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_s4 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_s4) s = Some (uvai_sd 20 192, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_s5 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_s5) s = Some (uvai_sd 21 200, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_s6 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_s6) s = Some (uvai_sd 22 208, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_s7 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_s7) s = Some (uvai_sd 23 216, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_s8 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_s8) s = Some (uvai_sd 24 224, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_s9 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_s9) s = Some (uvai_sd 25 232, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_s10 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_s10) s = Some (uvai_sd 26 240, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_s11 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_s11) s = Some (uvai_sd 27 248, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_t3 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_t3) s = Some (uvai_sd 28 256, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_t4 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_t4) s = Some (uvai_sd 29 264, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_t5 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_t5) s = Some (uvai_sd 30 272, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_t6 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_t6) s = Some (uvai_sd 31 280, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_sd_a0 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_sd_a0) s = Some (uvai_sd 5 112, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_ld_sp s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_ld_sp) s = Some (ai_ld 2 8, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_ld_tp s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_ld_tp) s = Some (ai_ld 4 32, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_ld_t0 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_ld_t0) s = Some (ai_ld 5 16, s).
Proof. decode_bridge_ms. Qed.

Lemma uvdec_ld_t1 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uvw_ld_t1) s = Some (ai_ld 6 0, s).
Proof. decode_bridge_ms. Qed.

(* --- compressed --- *)

Lemma uvdec_csd_s0 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uvh_csd_s0) s
  = Some (C_SD (mword_of_int 12, ucreg 2, ucreg 0), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma uvdec_csd_s1 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uvh_csd_s1) s
  = Some (C_SD (mword_of_int 13, ucreg 2, ucreg 1), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma uvdec_csd_a1 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uvh_csd_a1) s
  = Some (C_SD (mword_of_int 15, ucreg 2, ucreg 3), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma uvdec_csd_a2 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uvh_csd_a2) s
  = Some (C_SD (mword_of_int 16, ucreg 2, ucreg 4), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma uvdec_csd_a3 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uvh_csd_a3) s
  = Some (C_SD (mword_of_int 17, ucreg 2, ucreg 5), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma uvdec_csd_a4 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uvh_csd_a4) s
  = Some (C_SD (mword_of_int 18, ucreg 2, ucreg 6), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma uvdec_csd_a5 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uvh_csd_a5) s
  = Some (C_SD (mword_of_int 19, ucreg 2, ucreg 7), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma uvdec_cjalr_t0 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uvh_cjalr_t0) s
  = Some (C_JALR (ureg 5), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

(* ===================================================================== *)
(* 4. The [kernel_text]-backed [instr] constructors, by offset.           *)
(* ===================================================================== *)

Section UservecInstrs.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma uvi_csrw_sscratch :
    kernel_text -∗ instr (upa 0x00) false uvai_csrw_sscratch.
  Proof. mk_base (KernelSyms.trampoline + 0x00) uvw_csrw_sscratch (upa 0x00) uvai_csrw_sscratch uvdec_csrw_sscratch. Qed.

  Lemma uvi_lui :
    kernel_text -∗ instr (upa 0x04) false ai_lui.
  Proof. mk_base (KernelSyms.trampoline + 0x04) uw_lui (upa 0x04) ai_lui udec_lui. Qed.

  Lemma uvi_addiw :
    kernel_text -∗ instr (upa 0x08) true ai_addiw.
  Proof. mk_rvc (KernelSyms.trampoline + 0x08) uh_addiw (upa 0x08) ai_addiw udec_addiw exec_execute_C_ADDIW. Qed.

  Lemma uvi_slli :
    kernel_text -∗ instr (upa 0x0a) true ai_slli.
  Proof. mk_rvc (KernelSyms.trampoline + 0x0a) uh_slli (upa 0x0a) ai_slli udec_slli exec_execute_C_SLLI. Qed.

  Lemma uvi_sd_ra :
    kernel_text -∗ instr (upa 0x0c) false (uvai_sd 1 40).
  Proof. mk_base (KernelSyms.trampoline + 0x0c) uvw_sd_ra (upa 0x0c) (uvai_sd 1 40) uvdec_sd_ra. Qed.

  Lemma uvi_sd_sp :
    kernel_text -∗ instr (upa 0x10) false (uvai_sd 2 48).
  Proof. mk_base (KernelSyms.trampoline + 0x10) uvw_sd_sp (upa 0x10) (uvai_sd 2 48) uvdec_sd_sp. Qed.

  Lemma uvi_sd_gp :
    kernel_text -∗ instr (upa 0x14) false (uvai_sd 3 56).
  Proof. mk_base (KernelSyms.trampoline + 0x14) uvw_sd_gp (upa 0x14) (uvai_sd 3 56) uvdec_sd_gp. Qed.

  Lemma uvi_sd_tp :
    kernel_text -∗ instr (upa 0x18) false (uvai_sd 4 64).
  Proof. mk_base (KernelSyms.trampoline + 0x18) uvw_sd_tp (upa 0x18) (uvai_sd 4 64) uvdec_sd_tp. Qed.

  Lemma uvi_sd_t0 :
    kernel_text -∗ instr (upa 0x1c) false (uvai_sd 5 72).
  Proof. mk_base (KernelSyms.trampoline + 0x1c) uvw_sd_t0 (upa 0x1c) (uvai_sd 5 72) uvdec_sd_t0. Qed.

  Lemma uvi_sd_t1 :
    kernel_text -∗ instr (upa 0x20) false (uvai_sd 6 80).
  Proof. mk_base (KernelSyms.trampoline + 0x20) uvw_sd_t1 (upa 0x20) (uvai_sd 6 80) uvdec_sd_t1. Qed.

  Lemma uvi_sd_t2 :
    kernel_text -∗ instr (upa 0x24) false (uvai_sd 7 88).
  Proof. mk_base (KernelSyms.trampoline + 0x24) uvw_sd_t2 (upa 0x24) (uvai_sd 7 88) uvdec_sd_t2. Qed.

  Lemma uvi_csd_s0 :
    kernel_text -∗ instr (upa 0x28) true (uvai_csd_tgt 0 12).
  Proof. mk_rvc (KernelSyms.trampoline + 0x28) uvh_csd_s0 (upa 0x28) (uvai_csd_tgt 0 12) uvdec_csd_s0 exec_execute_C_SD. Qed.

  Lemma uvi_csd_s1 :
    kernel_text -∗ instr (upa 0x2a) true (uvai_csd_tgt 1 13).
  Proof. mk_rvc (KernelSyms.trampoline + 0x2a) uvh_csd_s1 (upa 0x2a) (uvai_csd_tgt 1 13) uvdec_csd_s1 exec_execute_C_SD. Qed.

  Lemma uvi_csd_a1 :
    kernel_text -∗ instr (upa 0x2c) true (uvai_csd_tgt 3 15).
  Proof. mk_rvc (KernelSyms.trampoline + 0x2c) uvh_csd_a1 (upa 0x2c) (uvai_csd_tgt 3 15) uvdec_csd_a1 exec_execute_C_SD. Qed.

  Lemma uvi_csd_a2 :
    kernel_text -∗ instr (upa 0x2e) true (uvai_csd_tgt 4 16).
  Proof. mk_rvc (KernelSyms.trampoline + 0x2e) uvh_csd_a2 (upa 0x2e) (uvai_csd_tgt 4 16) uvdec_csd_a2 exec_execute_C_SD. Qed.

  Lemma uvi_csd_a3 :
    kernel_text -∗ instr (upa 0x30) true (uvai_csd_tgt 5 17).
  Proof. mk_rvc (KernelSyms.trampoline + 0x30) uvh_csd_a3 (upa 0x30) (uvai_csd_tgt 5 17) uvdec_csd_a3 exec_execute_C_SD. Qed.

  Lemma uvi_csd_a4 :
    kernel_text -∗ instr (upa 0x32) true (uvai_csd_tgt 6 18).
  Proof. mk_rvc (KernelSyms.trampoline + 0x32) uvh_csd_a4 (upa 0x32) (uvai_csd_tgt 6 18) uvdec_csd_a4 exec_execute_C_SD. Qed.

  Lemma uvi_csd_a5 :
    kernel_text -∗ instr (upa 0x34) true (uvai_csd_tgt 7 19).
  Proof. mk_rvc (KernelSyms.trampoline + 0x34) uvh_csd_a5 (upa 0x34) (uvai_csd_tgt 7 19) uvdec_csd_a5 exec_execute_C_SD. Qed.

  Lemma uvi_sd_a6 :
    kernel_text -∗ instr (upa 0x36) false (uvai_sd 16 160).
  Proof. mk_base (KernelSyms.trampoline + 0x36) uvw_sd_a6 (upa 0x36) (uvai_sd 16 160) uvdec_sd_a6. Qed.

  Lemma uvi_sd_a7 :
    kernel_text -∗ instr (upa 0x3a) false (uvai_sd 17 168).
  Proof. mk_base (KernelSyms.trampoline + 0x3a) uvw_sd_a7 (upa 0x3a) (uvai_sd 17 168) uvdec_sd_a7. Qed.

  Lemma uvi_sd_s2 :
    kernel_text -∗ instr (upa 0x3e) false (uvai_sd 18 176).
  Proof. mk_base (KernelSyms.trampoline + 0x3e) uvw_sd_s2 (upa 0x3e) (uvai_sd 18 176) uvdec_sd_s2. Qed.

  Lemma uvi_sd_s3 :
    kernel_text -∗ instr (upa 0x42) false (uvai_sd 19 184).
  Proof. mk_base (KernelSyms.trampoline + 0x42) uvw_sd_s3 (upa 0x42) (uvai_sd 19 184) uvdec_sd_s3. Qed.

  Lemma uvi_sd_s4 :
    kernel_text -∗ instr (upa 0x46) false (uvai_sd 20 192).
  Proof. mk_base (KernelSyms.trampoline + 0x46) uvw_sd_s4 (upa 0x46) (uvai_sd 20 192) uvdec_sd_s4. Qed.

  Lemma uvi_sd_s5 :
    kernel_text -∗ instr (upa 0x4a) false (uvai_sd 21 200).
  Proof. mk_base (KernelSyms.trampoline + 0x4a) uvw_sd_s5 (upa 0x4a) (uvai_sd 21 200) uvdec_sd_s5. Qed.

  Lemma uvi_sd_s6 :
    kernel_text -∗ instr (upa 0x4e) false (uvai_sd 22 208).
  Proof. mk_base (KernelSyms.trampoline + 0x4e) uvw_sd_s6 (upa 0x4e) (uvai_sd 22 208) uvdec_sd_s6. Qed.

  Lemma uvi_sd_s7 :
    kernel_text -∗ instr (upa 0x52) false (uvai_sd 23 216).
  Proof. mk_base (KernelSyms.trampoline + 0x52) uvw_sd_s7 (upa 0x52) (uvai_sd 23 216) uvdec_sd_s7. Qed.

  Lemma uvi_sd_s8 :
    kernel_text -∗ instr (upa 0x56) false (uvai_sd 24 224).
  Proof. mk_base (KernelSyms.trampoline + 0x56) uvw_sd_s8 (upa 0x56) (uvai_sd 24 224) uvdec_sd_s8. Qed.

  Lemma uvi_sd_s9 :
    kernel_text -∗ instr (upa 0x5a) false (uvai_sd 25 232).
  Proof. mk_base (KernelSyms.trampoline + 0x5a) uvw_sd_s9 (upa 0x5a) (uvai_sd 25 232) uvdec_sd_s9. Qed.

  Lemma uvi_sd_s10 :
    kernel_text -∗ instr (upa 0x5e) false (uvai_sd 26 240).
  Proof. mk_base (KernelSyms.trampoline + 0x5e) uvw_sd_s10 (upa 0x5e) (uvai_sd 26 240) uvdec_sd_s10. Qed.

  Lemma uvi_sd_s11 :
    kernel_text -∗ instr (upa 0x62) false (uvai_sd 27 248).
  Proof. mk_base (KernelSyms.trampoline + 0x62) uvw_sd_s11 (upa 0x62) (uvai_sd 27 248) uvdec_sd_s11. Qed.

  Lemma uvi_sd_t3 :
    kernel_text -∗ instr (upa 0x66) false (uvai_sd 28 256).
  Proof. mk_base (KernelSyms.trampoline + 0x66) uvw_sd_t3 (upa 0x66) (uvai_sd 28 256) uvdec_sd_t3. Qed.

  Lemma uvi_sd_t4 :
    kernel_text -∗ instr (upa 0x6a) false (uvai_sd 29 264).
  Proof. mk_base (KernelSyms.trampoline + 0x6a) uvw_sd_t4 (upa 0x6a) (uvai_sd 29 264) uvdec_sd_t4. Qed.

  Lemma uvi_sd_t5 :
    kernel_text -∗ instr (upa 0x6e) false (uvai_sd 30 272).
  Proof. mk_base (KernelSyms.trampoline + 0x6e) uvw_sd_t5 (upa 0x6e) (uvai_sd 30 272) uvdec_sd_t5. Qed.

  Lemma uvi_sd_t6 :
    kernel_text -∗ instr (upa 0x72) false (uvai_sd 31 280).
  Proof. mk_base (KernelSyms.trampoline + 0x72) uvw_sd_t6 (upa 0x72) (uvai_sd 31 280) uvdec_sd_t6. Qed.

  Lemma uvi_csrr_sscratch :
    kernel_text -∗ instr (upa 0x76) false uvai_csrr_sscratch.
  Proof. mk_base (KernelSyms.trampoline + 0x76) uvw_csrr_sscratch (upa 0x76) uvai_csrr_sscratch uvdec_csrr_sscratch. Qed.

  Lemma uvi_sd_a0 :
    kernel_text -∗ instr (upa 0x7a) false (uvai_sd 5 112).
  Proof. mk_base (KernelSyms.trampoline + 0x7a) uvw_sd_a0 (upa 0x7a) (uvai_sd 5 112) uvdec_sd_a0. Qed.

  Lemma uvi_ld_sp :
    kernel_text -∗ instr (upa 0x7e) false (ai_ld 2 8).
  Proof. mk_base (KernelSyms.trampoline + 0x7e) uvw_ld_sp (upa 0x7e) (ai_ld 2 8) uvdec_ld_sp. Qed.

  Lemma uvi_ld_tp :
    kernel_text -∗ instr (upa 0x82) false (ai_ld 4 32).
  Proof. mk_base (KernelSyms.trampoline + 0x82) uvw_ld_tp (upa 0x82) (ai_ld 4 32) uvdec_ld_tp. Qed.

  Lemma uvi_ld_t0 :
    kernel_text -∗ instr (upa 0x86) false (ai_ld 5 16).
  Proof. mk_base (KernelSyms.trampoline + 0x86) uvw_ld_t0 (upa 0x86) (ai_ld 5 16) uvdec_ld_t0. Qed.

  Lemma uvi_ld_t1 :
    kernel_text -∗ instr (upa 0x8a) false (ai_ld 6 0).
  Proof. mk_base (KernelSyms.trampoline + 0x8a) uvw_ld_t1 (upa 0x8a) (ai_ld 6 0) uvdec_ld_t1. Qed.

  Lemma uvi_sfence1 :
    kernel_text -∗ instr (upa 0x8e) false ai_sfence.
  Proof. mk_base (KernelSyms.trampoline + 0x8e) uw_sfence (upa 0x8e) ai_sfence udec_sfence. Qed.

  Lemma uvi_csrw_satp :
    kernel_text -∗ instr (upa 0x92) false uvai_csrw_satp.
  Proof. mk_base (KernelSyms.trampoline + 0x92) uvw_csrw_satp (upa 0x92) uvai_csrw_satp uvdec_csrw_satp. Qed.

  Lemma uvi_sfence2 :
    kernel_text -∗ instr (upa 0x96) false ai_sfence.
  Proof. mk_base (KernelSyms.trampoline + 0x96) uw_sfence (upa 0x96) ai_sfence udec_sfence. Qed.

  Lemma uvi_cjalr_t0 :
    kernel_text -∗ instr (upa 0x9a) true uvai_jalr_t0.
  Proof. mk_rvc (KernelSyms.trampoline + 0x9a) uvh_cjalr_t0 (upa 0x9a) uvai_jalr_t0 uvdec_cjalr_t0 exec_execute_C_JALR. Qed.

End UservecInstrs.
