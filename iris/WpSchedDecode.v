(* WpSchedDecode.v -- decode templates + [instr] facts for sched()'s
   instructions at KernelSyms.sched = 0x80001e1e.

   sched's 48-byte frame prologue/epilogue (c.addi16sp -48 / five c.sdsp /
   c.addi4spn / five c.ldsp / c.addi16sp +48 / c.ret) is byte-identical to
   freerange's, so those decodes reuse [fdc_*] from WpFreerangeDecode.v; the
   a5-materialization triples (c.mv a5,tp / sext.w / c.slli a5,7) reuse
   [mydec_mv]/[mydec_addiw]/[mydec_slli] from WpMycpu.v; c.ret reuses
   podec_2a.  The remaining words -- the two panic-guard c.li's, the c.lw of
   p->state, the two c.add's onto pid_lock, c.mv s1,a0, c.beqz/c.bnez guards,
   c.andi, c.addi a5,8, the three per-CPU c.add's, the csrr, the two lw's, the
   sw, the auipc/addi pairs and the two jal's -- are sched's own and get fresh
   templates here.  The four panic arms after +0x8a are never executed and get
   no decode facts. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode KernelText.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Import WpMycpu.
Require Import WpFreerangeDecode.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.

Notation SD := KernelSyms.sched.

(* ===================================================================== *)
(* Fresh compressed decode templates.                                     *)
(* ===================================================================== *)

(* +0x12  0x84aa  c.mv s1,a0 *)
Lemma sddec_mv_s1_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x84aa : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x18  0xc935  c.beqz a0,<panic> *)
Lemma sddec_beqz_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc935 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 58, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x28  0x97ba  c.add a5,a5,a4 *)
Lemma sddec_add_a5_a4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x97ba : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 15), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x2e  0x4785  c.li a5,1 *)
Lemma sddec_li_a5_1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4785 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x34  0x4c98  c.lw a4,24(s1) *)
Lemma sddec_lw_a4_24 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4c98 : mword 16)) s
  = Some (C_LW (mword_of_int 6, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* the specialized C_LW -> LOAD bridge in the leaf-friendly (Regidx / mword_of_int)
   form (mirror of KernelRvcDecode.poexec_lw). *)
Lemma sd_cr1 : creg2reg_idx (Cregidx (mword_of_int 1)) = Regidx (mword_of_int 9).
Proof. vm_compute. reflexivity. Qed.
Lemma sd_cr6 : creg2reg_idx (Cregidx (mword_of_int 6)) = Regidx (mword_of_int 14).
Proof. vm_compute. reflexivity. Qed.
Lemma sd_imm24 : zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00")) = (mword_of_int 24 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma sdexec_lw24 s :
  exec (execute (C_LW (mword_of_int 6, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 24, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_LW. cbn zeta.
  rewrite exec_returnM. rewrite sd_cr1 sd_cr6 sd_imm24. reflexivity.
Qed.

(* +0x36  0x4791  c.li a5,4 *)
Lemma sddec_li_a5_4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4791 : mword 16)) s
  = Some (C_LI (mword_of_int 4, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x40  0x8b89  c.andi a5,a5,2 *)
Lemma sddec_andi_a5_2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8b89 : mword 16)) s
  = Some (C_ANDI (mword_of_int 2, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma sdexec_andi2 s :
  exec (execute (C_ANDI (mword_of_int 2, Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_ANDI. cbn zeta.
  rewrite exec_returnM. rewrite !po_cr7. reflexivity.
Qed.

(* +0x42  0xe7bd  c.bnez a5,<panic> *)
Lemma sddec_bnez_a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe7bd : mword 16)) s
  = Some (C_BNEZ (mword_of_int 55, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x52  0x97ca  c.add a5,a5,s2 *)
Lemma sddec_add_a5_s2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x97ca : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 15), Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x5e  0x07a1  c.addi a5,a5,8 *)
Lemma sddec_addi_a5_8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x07a1 : mword 16)) s
  = Some (C_ADDI (mword_of_int 8, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x68  0x95be  c.add a1,a1,a5 *)
Lemma sddec_add_a1_a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x95be : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 11), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x78  0x993e  c.add s2,s2,a5 *)
Lemma sddec_add_s2_a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x993e : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 18), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Fresh base (32-bit) decode templates.                                  *)
(* ===================================================================== *)

(* +0x0e  0xad9ff0ef  jal ra,myproc (target 0x80001904; offset -1320) *)
Lemma sddec_jal_myproc s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xad9ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095832 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x14  0xd71fe0ef  jal ra,holding (target 0x80000ba2; offset -4752) *)
Lemma sddec_jal_holding s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd71fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092400 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x20  0x00010717  auipc a4,0x10 *)
Lemma sddec_auipc_a4 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00010717 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 14), AUIPC), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x24  0x50a70713  addi a4,a4,1290 *)
Lemma sddec_addi_a4 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x50a70713 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x50a : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x2a  0x0a87a703  lw a4,168(a5) *)
Lemma sddec_lw_a4_168 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0a87a703 : mword 32)) s
  = Some (LOAD (mword_of_int 168 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 4), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x30  0x06f71463  bne a4,a5,<panic> *)
Lemma sddec_bne s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x06f71463 : mword 32)) s
  = Some (BTYPE (mword_of_int 104 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x38  0x06f70663  beq a4,a5,<panic> *)
Lemma sddec_beq s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x06f70663 : mword 32)) s
  = Some (BTYPE (mword_of_int 108 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x3c  0x100027f3  csrr a5,sstatus  (csrrs a5,sstatus,x0) *)
Lemma sddec_csrr s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x100027f3 : mword 32)) s
  = Some (CSRReg (Ox"100", Regidx (mword_of_int 0), Regidx (mword_of_int 15), CSRRS), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x46  0x00010917  auipc s2,0x10 *)
Lemma sddec_auipc_s2 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00010917 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 18), AUIPC), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x4a  0x4e490913  addi s2,s2,1252 *)
Lemma sddec_addi_s2 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4e490913 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x4e4 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x54  0x0ac7a983  lw s3,172(a5) *)
Lemma sddec_lw_s3_172 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0ac7a983 : mword 32)) s
  = Some (LOAD (mword_of_int 172 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 19), false, 4), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x60  0x00010597  auipc a1,0x10 *)
Lemma sddec_auipc_a1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00010597 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x64  0x4fa58593  addi a1,a1,1274 *)
Lemma sddec_addi_a1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4fa58593 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x4fa : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x6a  0x06048513  addi a0,s1,96 *)
Lemma sddec_addi_a0 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x06048513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x60 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x6e  0x50c000ef  jal swtch (target 0x80002398) *)
Lemma sddec_jal_swtch s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x50c000ef : mword 32)) s
  = Some (JAL (mword_of_int 1292 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x7a  0x0b392623  sw s3,172(s2) *)
Lemma sddec_sw_s3_172 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0b392623 : mword 32)) s
  = Some (STORE (mword_of_int 172 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 18), 4), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Section WpSchedDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ---- prologue: 48-byte frame, saves ra/s0/s1/s2/s3 (freerange decodes) ---- *)
  Lemma sdi_00 : kernel_text -∗ instr (mword_of_int (SD + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SD + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (SD + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) fdc_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma sdi_02 : kernel_text -∗ instr (mword_of_int (SD + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (SD + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (SD + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) fdc_f406 exec_execute_C_SDSP. Qed.

  Lemma sdi_04 : kernel_text -∗ instr (mword_of_int (SD + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (SD + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (SD + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) fdc_f022 exec_execute_C_SDSP. Qed.

  Lemma sdi_06 : kernel_text -∗ instr (mword_of_int (SD + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (SD + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (SD + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) fdc_ec26 exec_execute_C_SDSP. Qed.

  Lemma sdi_08 : kernel_text -∗ instr (mword_of_int (SD + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (SD + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (SD + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) fdc_e84a exec_execute_C_SDSP. Qed.

  Lemma sdi_0a : kernel_text -∗ instr (mword_of_int (SD + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (SD + 0x0a)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (SD + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) fdc_e44e exec_execute_C_SDSP. Qed.

  Lemma sdi_0c : kernel_text -∗ instr (mword_of_int (SD + 0x0c) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (SD + 0x0c)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (SD + 0x0c) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) fdc_1800 exec_execute_C_ADDI4SPN. Qed.

  (* ---- +0x0e: jal myproc (target 0x80001904) ---- *)
  Lemma sdi_0e : kernel_text -∗ instr (mword_of_int (SD + 0x0e) : mword 64) false (JAL (mword_of_int 2095832 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SD + 0x0e)%Z (mword_of_int 0xad9ff0ef : mword 32)
    (mword_of_int (SD + 0x0e) : mword 64) (JAL (mword_of_int 2095832 : mword 21, Regidx (mword_of_int 1))) sddec_jal_myproc. Qed.

  (* ---- +0x12: c.mv s1,a0 ---- *)
  Lemma sdi_12 : kernel_text -∗ instr (mword_of_int (SD + 0x12) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (SD + 0x12)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (SD + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) sddec_mv_s1_a0 exec_execute_C_MV. Qed.

  (* ---- +0x14: jal holding (target 0x80000ba2) ---- *)
  Lemma sdi_14 : kernel_text -∗ instr (mword_of_int (SD + 0x14) : mword 64) false (JAL (mword_of_int 2092400 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SD + 0x14)%Z (mword_of_int 0xd71fe0ef : mword 32)
    (mword_of_int (SD + 0x14) : mword 64) (JAL (mword_of_int 2092400 : mword 21, Regidx (mword_of_int 1))) sddec_jal_holding. Qed.

  (* ---- +0x18: c.beqz a0,<panic> ---- *)
  Lemma sdi_18 : kernel_text -∗ instr (mword_of_int (SD + 0x18) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 58 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (SD + 0x18)%Z (mword_of_int 0xc935 : mword 16)
    (mword_of_int (SD + 0x18) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 58 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) sddec_beqz_a0 exec_execute_C_BEQZ. Qed.

  (* ---- +0x1a..+0x1e: c.mv a5,tp / sext.w a5 / c.slli a5,7 (mycpu decodes) ---- *)
  Lemma sdi_1a : kernel_text -∗ instr (mword_of_int (SD + 0x1a) : mword 64) true (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (SD + 0x1a)%Z (mword_of_int 0x8792 : mword 16)
    (mword_of_int (SD + 0x1a) : mword 64) (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)) mydec_mv exec_execute_C_MV. Qed.

  Lemma sdi_1c : kernel_text -∗ instr (mword_of_int (SD + 0x1c) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (SD + 0x1c)%Z (mword_of_int 0x2781 : mword 16)
    (mword_of_int (SD + 0x1c) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) mydec_addiw exec_execute_C_ADDIW. Qed.

  Lemma sdi_1e : kernel_text -∗ instr (mword_of_int (SD + 0x1e) : mword 64) true (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (SD + 0x1e)%Z (mword_of_int 0x079e : mword 16)
    (mword_of_int (SD + 0x1e) : mword 64) (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) mydec_slli exec_execute_C_SLLI. Qed.

  (* ---- +0x20: auipc a4,0x10 ---- *)
  Lemma sdi_20 : kernel_text -∗ instr (mword_of_int (SD + 0x20) : mword 64) false (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (SD + 0x20)%Z (mword_of_int 0x00010717 : mword 32)
    (mword_of_int (SD + 0x20) : mword 64) (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 14), AUIPC)) sddec_auipc_a4. Qed.

  (* ---- +0x24: addi a4,a4,1290 ---- *)
  Lemma sdi_24 : kernel_text -∗ instr (mword_of_int (SD + 0x24) : mword 64) false (ITYPE (mword_of_int 0x50a : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (SD + 0x24)%Z (mword_of_int 0x50a70713 : mword 32)
    (mword_of_int (SD + 0x24) : mword 64) (ITYPE (mword_of_int 0x50a : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) sddec_addi_a4. Qed.

  (* ---- +0x28: c.add a5,a5,a4 ---- *)
  Lemma sdi_28 : kernel_text -∗ instr (mword_of_int (SD + 0x28) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (SD + 0x28)%Z (mword_of_int 0x97ba : mword 16)
    (mword_of_int (SD + 0x28) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) sddec_add_a5_a4 exec_execute_C_ADD. Qed.

  (* ---- +0x2a: lw a4,168(a5) ---- *)
  Lemma sdi_2a : kernel_text -∗ instr (mword_of_int (SD + 0x2a) : mword 64) false (LOAD (mword_of_int 168 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_base (SD + 0x2a)%Z (mword_of_int 0x0a87a703 : mword 32)
    (mword_of_int (SD + 0x2a) : mword 64) (LOAD (mword_of_int 168 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 4)) sddec_lw_a4_168. Qed.

  (* ---- +0x2e: c.li a5,1 ---- *)
  Lemma sdi_2e : kernel_text -∗ instr (mword_of_int (SD + 0x2e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SD + 0x2e)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (SD + 0x2e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) sddec_li_a5_1 exec_execute_C_LI. Qed.

  (* ---- +0x30: bne a4,a5,<panic> ---- *)
  Lemma sdi_30 : kernel_text -∗ instr (mword_of_int (SD + 0x30) : mword 64) false (BTYPE (mword_of_int 104 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE)).
  Proof. mk_base (SD + 0x30)%Z (mword_of_int 0x06f71463 : mword 32)
    (mword_of_int (SD + 0x30) : mword 64) (BTYPE (mword_of_int 104 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE)) sddec_bne. Qed.

  (* ---- +0x34: c.lw a4,24(s1) ---- *)
  Lemma sdi_34 : kernel_text -∗ instr (mword_of_int (SD + 0x34) : mword 64) true (LOAD (mword_of_int 24, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_rvc (SD + 0x34)%Z (mword_of_int 0x4c98 : mword 16)
    (mword_of_int (SD + 0x34) : mword 64) (LOAD (mword_of_int 24, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)) sddec_lw_a4_24 sdexec_lw24. Qed.

  (* ---- +0x36: c.li a5,4 ---- *)
  Lemma sdi_36 : kernel_text -∗ instr (mword_of_int (SD + 0x36) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SD + 0x36)%Z (mword_of_int 0x4791 : mword 16)
    (mword_of_int (SD + 0x36) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) sddec_li_a5_4 exec_execute_C_LI. Qed.

  (* ---- +0x38: beq a4,a5,<panic> ---- *)
  Lemma sdi_38 : kernel_text -∗ instr (mword_of_int (SD + 0x38) : mword 64) false (BTYPE (mword_of_int 108 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)).
  Proof. mk_base (SD + 0x38)%Z (mword_of_int 0x06f70663 : mword 32)
    (mword_of_int (SD + 0x38) : mword 64) (BTYPE (mword_of_int 108 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)) sddec_beq. Qed.

  (* ---- +0x3c: csrr a5,sstatus ---- *)
  Lemma sdi_3c : kernel_text -∗ instr (mword_of_int (SD + 0x3c) : mword 64) false (CSRReg (Ox"100", Regidx (mword_of_int 0), Regidx (mword_of_int 15), CSRRS)).
  Proof. mk_base (SD + 0x3c)%Z (mword_of_int 0x100027f3 : mword 32)
    (mword_of_int (SD + 0x3c) : mword 64) (CSRReg (Ox"100", Regidx (mword_of_int 0), Regidx (mword_of_int 15), CSRRS)) sddec_csrr. Qed.

  (* ---- +0x40: c.andi a5,a5,2 ---- *)
  Lemma sdi_40 : kernel_text -∗ instr (mword_of_int (SD + 0x40) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_rvc (SD + 0x40)%Z (mword_of_int 0x8b89 : mword 16)
    (mword_of_int (SD + 0x40) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) sddec_andi_a5_2 sdexec_andi2. Qed.

  (* ---- +0x42: c.bnez a5,<panic> ---- *)
  Lemma sdi_42 : kernel_text -∗ instr (mword_of_int (SD + 0x42) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 55 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (SD + 0x42)%Z (mword_of_int 0xe7bd : mword 16)
    (mword_of_int (SD + 0x42) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 55 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) sddec_bnez_a5 exec_execute_C_BNEZ. Qed.

  (* ---- +0x44..+0x50: c.mv a5,tp / sext.w / c.slli a5,7 ---- *)
  Lemma sdi_44 : kernel_text -∗ instr (mword_of_int (SD + 0x44) : mword 64) true (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (SD + 0x44)%Z (mword_of_int 0x8792 : mword 16)
    (mword_of_int (SD + 0x44) : mword 64) (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)) mydec_mv exec_execute_C_MV. Qed.

  (* ---- +0x46: auipc s2,0x10 ---- *)
  Lemma sdi_46 : kernel_text -∗ instr (mword_of_int (SD + 0x46) : mword 64) false (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 18), AUIPC)).
  Proof. mk_base (SD + 0x46)%Z (mword_of_int 0x00010917 : mword 32)
    (mword_of_int (SD + 0x46) : mword 64) (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 18), AUIPC)) sddec_auipc_s2. Qed.

  (* ---- +0x4a: addi s2,s2,1252 ---- *)
  Lemma sdi_4a : kernel_text -∗ instr (mword_of_int (SD + 0x4a) : mword 64) false (ITYPE (mword_of_int 0x4e4 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (SD + 0x4a)%Z (mword_of_int 0x4e490913 : mword 32)
    (mword_of_int (SD + 0x4a) : mword 64) (ITYPE (mword_of_int 0x4e4 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) sddec_addi_s2. Qed.

  (* ---- +0x4e: sext.w a5 ---- *)
  Lemma sdi_4e : kernel_text -∗ instr (mword_of_int (SD + 0x4e) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (SD + 0x4e)%Z (mword_of_int 0x2781 : mword 16)
    (mword_of_int (SD + 0x4e) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) mydec_addiw exec_execute_C_ADDIW. Qed.

  (* ---- +0x50: c.slli a5,7 ---- *)
  Lemma sdi_50 : kernel_text -∗ instr (mword_of_int (SD + 0x50) : mword 64) true (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (SD + 0x50)%Z (mword_of_int 0x079e : mword 16)
    (mword_of_int (SD + 0x50) : mword 64) (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) mydec_slli exec_execute_C_SLLI. Qed.

  (* ---- +0x52: c.add a5,a5,s2 ---- *)
  Lemma sdi_52 : kernel_text -∗ instr (mword_of_int (SD + 0x52) : mword 64) true (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (SD + 0x52)%Z (mword_of_int 0x97ca : mword 16)
    (mword_of_int (SD + 0x52) : mword 64) (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) sddec_add_a5_s2 exec_execute_C_ADD. Qed.

  (* ---- +0x54: lw s3,172(a5) ---- *)
  Lemma sdi_54 : kernel_text -∗ instr (mword_of_int (SD + 0x54) : mword 64) false (LOAD (mword_of_int 172 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 19), false, 4)).
  Proof. mk_base (SD + 0x54)%Z (mword_of_int 0x0ac7a983 : mword 32)
    (mword_of_int (SD + 0x54) : mword 64) (LOAD (mword_of_int 172 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 19), false, 4)) sddec_lw_s3_172. Qed.

  (* ---- +0x58..+0x5c: c.mv a5,tp / sext.w / c.slli a5,7 ---- *)
  Lemma sdi_58 : kernel_text -∗ instr (mword_of_int (SD + 0x58) : mword 64) true (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (SD + 0x58)%Z (mword_of_int 0x8792 : mword 16)
    (mword_of_int (SD + 0x58) : mword 64) (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)) mydec_mv exec_execute_C_MV. Qed.

  Lemma sdi_5a : kernel_text -∗ instr (mword_of_int (SD + 0x5a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (SD + 0x5a)%Z (mword_of_int 0x2781 : mword 16)
    (mword_of_int (SD + 0x5a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) mydec_addiw exec_execute_C_ADDIW. Qed.

  Lemma sdi_5c : kernel_text -∗ instr (mword_of_int (SD + 0x5c) : mword 64) true (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (SD + 0x5c)%Z (mword_of_int 0x079e : mword 16)
    (mword_of_int (SD + 0x5c) : mword 64) (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) mydec_slli exec_execute_C_SLLI. Qed.

  (* ---- +0x5e: c.addi a5,a5,8 ---- *)
  Lemma sdi_5e : kernel_text -∗ instr (mword_of_int (SD + 0x5e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SD + 0x5e)%Z (mword_of_int 0x07a1 : mword 16)
    (mword_of_int (SD + 0x5e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) sddec_addi_a5_8 exec_execute_C_ADDI. Qed.

  (* ---- +0x60: auipc a1,0x10 ---- *)
  Lemma sdi_60 : kernel_text -∗ instr (mword_of_int (SD + 0x60) : mword 64) false (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (SD + 0x60)%Z (mword_of_int 0x00010597 : mword 32)
    (mword_of_int (SD + 0x60) : mword 64) (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 11), AUIPC)) sddec_auipc_a1. Qed.

  (* ---- +0x64: addi a1,a1,1274 ---- *)
  Lemma sdi_64 : kernel_text -∗ instr (mword_of_int (SD + 0x64) : mword 64) false (ITYPE (mword_of_int 0x4fa : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (SD + 0x64)%Z (mword_of_int 0x4fa58593 : mword 32)
    (mword_of_int (SD + 0x64) : mword 64) (ITYPE (mword_of_int 0x4fa : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) sddec_addi_a1. Qed.

  (* ---- +0x68: c.add a1,a1,a5 ---- *)
  Lemma sdi_68 : kernel_text -∗ instr (mword_of_int (SD + 0x68) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (SD + 0x68)%Z (mword_of_int 0x95be : mword 16)
    (mword_of_int (SD + 0x68) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADD)) sddec_add_a1_a5 exec_execute_C_ADD. Qed.

  (* ---- +0x6a: addi a0,s1,96 ---- *)
  Lemma sdi_6a : kernel_text -∗ instr (mword_of_int (SD + 0x6a) : mword 64) false (ITYPE (mword_of_int 0x60 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (SD + 0x6a)%Z (mword_of_int 0x06048513 : mword 32)
    (mword_of_int (SD + 0x6a) : mword 64) (ITYPE (mword_of_int 0x60 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)) sddec_addi_a0. Qed.

  (* ---- +0x6e: jal swtch ---- *)
  Lemma sdi_6e : kernel_text -∗ instr (mword_of_int (SD + 0x6e) : mword 64) false (JAL (mword_of_int 1292 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SD + 0x6e)%Z (mword_of_int 0x50c000ef : mword 32)
    (mword_of_int (SD + 0x6e) : mword 64) (JAL (mword_of_int 1292 : mword 21, Regidx (mword_of_int 1))) sddec_jal_swtch. Qed.

  (* ---- +0x72..+0x76: c.mv a5,tp / sext.w / c.slli a5,7 ---- *)
  Lemma sdi_72 : kernel_text -∗ instr (mword_of_int (SD + 0x72) : mword 64) true (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (SD + 0x72)%Z (mword_of_int 0x8792 : mword 16)
    (mword_of_int (SD + 0x72) : mword 64) (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)) mydec_mv exec_execute_C_MV. Qed.

  Lemma sdi_74 : kernel_text -∗ instr (mword_of_int (SD + 0x74) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (SD + 0x74)%Z (mword_of_int 0x2781 : mword 16)
    (mword_of_int (SD + 0x74) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) mydec_addiw exec_execute_C_ADDIW. Qed.

  Lemma sdi_76 : kernel_text -∗ instr (mword_of_int (SD + 0x76) : mword 64) true (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (SD + 0x76)%Z (mword_of_int 0x079e : mword 16)
    (mword_of_int (SD + 0x76) : mword 64) (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) mydec_slli exec_execute_C_SLLI. Qed.

  (* ---- +0x78: c.add s2,s2,a5 ---- *)
  Lemma sdi_78 : kernel_text -∗ instr (mword_of_int (SD + 0x78) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (SD + 0x78)%Z (mword_of_int 0x993e : mword 16)
    (mword_of_int (SD + 0x78) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)) sddec_add_s2_a5 exec_execute_C_ADD. Qed.

  (* ---- +0x7a: sw s3,172(s2) ---- *)
  Lemma sdi_7a : kernel_text -∗ instr (mword_of_int (SD + 0x7a) : mword 64) false (STORE (mword_of_int 172 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 18), 4)).
  Proof. mk_base (SD + 0x7a)%Z (mword_of_int 0x0b392623 : mword 32)
    (mword_of_int (SD + 0x7a) : mword 64) (STORE (mword_of_int 172 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 18), 4)) sddec_sw_s3_172. Qed.

  (* ---- +0x7e..+0x86: c.ldsp ra/s0/s1/s2/s3 (freerange decodes) ---- *)
  Lemma sdi_7e : kernel_text -∗ instr (mword_of_int (SD + 0x7e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (SD + 0x7e)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (SD + 0x7e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) fdc_70a2 exec_execute_C_LDSP. Qed.

  Lemma sdi_80 : kernel_text -∗ instr (mword_of_int (SD + 0x80) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (SD + 0x80)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (SD + 0x80) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) fdc_7402 exec_execute_C_LDSP. Qed.

  Lemma sdi_82 : kernel_text -∗ instr (mword_of_int (SD + 0x82) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (SD + 0x82)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (SD + 0x82) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) fdc_64e2 exec_execute_C_LDSP. Qed.

  Lemma sdi_84 : kernel_text -∗ instr (mword_of_int (SD + 0x84) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (SD + 0x84)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (SD + 0x84) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) fdc_6942 exec_execute_C_LDSP. Qed.

  Lemma sdi_86 : kernel_text -∗ instr (mword_of_int (SD + 0x86) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (SD + 0x86)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (SD + 0x86) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) fdc_69a2 exec_execute_C_LDSP. Qed.

  (* ---- +0x88: c.addi16sp sp,48 ---- *)
  Lemma sdi_88 : kernel_text -∗ instr (mword_of_int (SD + 0x88) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SD + 0x88)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (SD + 0x88) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) fdc_6145 exec_execute_C_ADDI16SP. Qed.

  (* ---- +0x8a: c.ret ---- *)
  Lemma sdi_8a : kernel_text -∗ instr (mword_of_int (SD + 0x8a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (SD + 0x8a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (SD + 0x8a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) podec_2a exec_execute_C_JR. Qed.

End WpSchedDecode.
