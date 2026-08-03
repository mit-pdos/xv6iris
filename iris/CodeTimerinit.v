(* CodeTimerinit.v -- the machine code of timerinit(): the decode templates for the
   words this function alone uses, and the [instr] constructors for its
   instruction addresses.  Consumed by WpTimerinit.v. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras WpDecode WpGpr.
Require Import WpMmodeShiftiop.
Require Import WpMmodeLeafBase.
Require Import WpMmodeUtype.
Require Import WpMmodeItype.
Require Import WpMmodeRtype.
Require Import WpMmodeJalr.
Require Import WpMmodeLoad.
Require Import WpMmodeStore.
Require Import WpGprCsrrA WpGprCsrrB WpGprCsrwA WpGprCsrwB.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpRvcBridge.
Require Import StackOwn.
Require Import RegFile.
From iris.base_logic.lib Require Import invariants.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.


(* ===================================================================== *)
(* Canonical operand values.  Registers as [mword 5] literals; the        *)
(* stack pointer reuses WpGprRvc's [csp_rs1] (so the c.sdsp/c.ldsp ea     *)
(* forms need no key bridging).                                           *)
(* ===================================================================== *)
Definition ti_ra : mword 5 := mword_of_int 1.    (* x1  *)
Definition ti_s0 : mword 5 := mword_of_int 8.    (* x8  *)
Definition ti_a4 : mword 5 := mword_of_int 14.   (* x14 *)
Definition ti_a5 : mword 5 := mword_of_int 15.   (* x15 *)
Definition ti_cs0 : cregidx := Cregidx (mword_of_int 0).  (* x8  as creg *)
Definition ti_ca4 : cregidx := Cregidx (mword_of_int 6).  (* x14 as creg *)
Definition ti_ca5 : cregidx := Cregidx (mword_of_int 7).  (* x15 as creg *)

Definition i9   : mword 6  := mword_of_int 48.   (* c.addi imm = -16 (6-bit) *)
Definition u10  : mword 6  := mword_of_int 1.    (* c.sdsp/c.ldsp ra offset 8  *)
Definition u11  : mword 6  := mword_of_int 0.    (* c.sdsp/c.ldsp s0 offset 0  *)
Definition nz12 : mword 8  := mword_of_int 4.    (* c.addi4spn nzimm (16/4)    *)
Definition i14  : mword 6  := mword_of_int 63.   (* c.li imm = -1 (6-bit)      *)
Definition sh15 : mword 6  := mword_of_int 63.   (* c.slli shamt               *)
Definition i19  : mword 12 := mword_of_int 2.    (* ori imm                    *)
Definition i22  : mword 20 := mword_of_int 0xf4. (* lui imm                    *)
Definition i23  : mword 12 := mword_of_int 576.  (* addi imm                   *)
Definition i28  : mword 6  := mword_of_int 16.   (* c.addi imm = +16           *)

(* the RVC halfwords and, for the 4-aligned RVC sites, the whole 4-byte
   fetch-window words (low 16 = the RVC encoding, high 16 = the next
   instruction's low bytes, exactly as the image stores them). *)
Definition ti_h9  : mword 16 := mword_of_int 0x1141.
Definition ti_h10 : mword 16 := mword_of_int 0xe406.
Definition ti_h11 : mword 16 := mword_of_int 0xe022.
Definition ti_h12 : mword 16 := mword_of_int 0x0800.
Definition ti_w13 : mword 32 := mword_of_int 0x30a027f3.
Definition ti_h14 : mword 16 := mword_of_int 0x577d.
Definition ti_h15 : mword 16 := mword_of_int 0x177e.
Definition ti_h16 : mword 16 := mword_of_int 0x8fd9.
Definition ti_w17 : mword 32 := mword_of_int 0x30a79073.
Definition ti_w18 : mword 32 := mword_of_int 0x306027f3.
Definition ti_w19 : mword 32 := mword_of_int 0x0027e793.
Definition ti_w20 : mword 32 := mword_of_int 0x30679073.
Definition ti_w21 : mword 32 := mword_of_int 0xc01027f3.
Definition ti_w22 : mword 32 := mword_of_int 0x000f4737.
Definition ti_w23 : mword 32 := mword_of_int 0x24070713.
Definition ti_h24 : mword 16 := mword_of_int 0x97ba.
Definition ti_w25 : mword 32 := mword_of_int 0x14d79073.
Definition ti_h26 : mword 16 := mword_of_int 0x60a2.
Definition ti_h27 : mword 16 := mword_of_int 0x6402.
Definition ti_h28 : mword 16 := mword_of_int 0x0141.
Definition ti_h29 : mword 16 := mword_of_int 0x8082.

(* ===================================================================== *)
(* Decode lemmas.  RVC: concrete compressed words decode through            *)
(* [rvc_oneshot] (WpRvcBridge); 32-bit: [decode_any] one-shot.             *)
(* ===================================================================== *)

(* ---- idx 9: 0x1141 -> c.addi sp, -16 ---- *)
Lemma ti_decode9 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h9) s = Some (C_ADDI (i9, Regidx csp_rs1), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 10: 0xe406 -> c.sdsp ra, 8(sp) ---- *)
Lemma ti_decode10 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h10) s = Some (C_SDSP (u10, Regidx ti_ra), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 11: 0xe022 -> c.sdsp s0, 0(sp) ---- *)
Lemma ti_decode11 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h11) s = Some (C_SDSP (u11, Regidx ti_s0), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 12: 0x0800 -> c.addi4spn s0, sp, 16 ---- *)
Lemma ti_decode12 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h12) s = Some (C_ADDI4SPN (ti_cs0, nz12), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 14: 0x577d -> c.li a4, -1 ---- *)
Lemma ti_decode14 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h14) s = Some (C_LI (i14, Regidx ti_a4), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 15: 0x177e -> c.slli a4, 63 ---- *)
Lemma ti_decode15 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h15) s = Some (C_SLLI (sh15, Regidx ti_a4), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 16: 0x8fd9 -> c.or a5, a4 ---- *)
Lemma ti_decode16 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h16) s = Some (C_OR (ti_ca5, ti_ca4), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 24: 0x97ba -> c.add a5, a4 ---- *)
Lemma ti_decode24 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h24) s = Some (C_ADD (Regidx ti_a5, Regidx ti_a4), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 26: 0x60a2 -> c.ldsp ra, 8(sp) ---- *)
Lemma ti_decode26 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h26) s = Some (C_LDSP (u10, Regidx ti_ra), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 27: 0x6402 -> c.ldsp s0, 0(sp) ---- *)
Lemma ti_decode27 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h27) s = Some (C_LDSP (u11, Regidx ti_s0), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 28: 0x0141 -> c.addi sp, 16 ---- *)
Lemma ti_decode28 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h28) s = Some (C_ADDI (i28, Regidx csp_rs1), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 29: 0x8082 -> c.ret = c.jr ra ---- *)
Lemma ti_decode29 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h29) s = Some (C_JR (Regidx ti_ra), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- the nine 32-bit instructions: one-shot [decode_any] ---- *)
Lemma ti_decode13 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode ti_w13) s
    = Some (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma ti_decode17 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode ti_w17) s
    = Some (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma ti_decode18 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode ti_w18) s
    = Some (CSRReg (WpGprCsrrA.csr_mcounteren, zreg, Regidx ti_a5, CSRRS), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma ti_decode19 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode ti_w19) s
    = Some (ITYPE (i19, Regidx ti_a5, Regidx ti_a5, ORI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma ti_decode20 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode ti_w20) s
    = Some (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx ti_a5, zreg, CSRRW), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma ti_decode21 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode ti_w21) s
    = Some (CSRReg (WpGprCsrrB.csr_time, zreg, Regidx ti_a5, CSRRS), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma ti_decode22 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode ti_w22) s
    = Some (UTYPE (i22, Regidx ti_a4, LUI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma ti_decode23 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode ti_w23) s
    = Some (ITYPE (i23, Regidx ti_a4, Regidx ti_a4, ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma ti_decode25 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode ti_w25) s
    = Some (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx ti_a5, zreg, CSRRW), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* ===================================================================== *)
(* The 21 [instr] constructors from [kernel_text] (WpEntryNew recipe).    *)
(* ===================================================================== *)
(* discharge [wp_instr]'s per-byte static premise at a concrete boot pc:
   M-mode fetch is untranslated, so the identity/static window is guard-permitted. *)
Ltac boot_static :=
  apply KptPt.instr_window_static; intros jj Hjj; unfold addr_is_text;
  destruct jj as [|[|[|[|]]]]; try lia;
  (split; [vm_compute; discriminate | vm_compute; reflexivity]).

Section WpTimerinit.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* PCs of the 21 instructions. *)
  Definition ti_pc9  : mword 64 := mword_of_int (KernelSyms.timerinit).
  Definition ti_pc10 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x2).
  Definition ti_pc11 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x4).
  Definition ti_pc12 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x6).
  Definition ti_pc13 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x8).
  Definition ti_pc14 : mword 64 := mword_of_int (KernelSyms.timerinit + 0xc).
  Definition ti_pc15 : mword 64 := mword_of_int (KernelSyms.timerinit + 0xe).
  Definition ti_pc16 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x10).
  Definition ti_pc17 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x12).
  Definition ti_pc18 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x16).
  Definition ti_pc19 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x1a).
  Definition ti_pc20 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x1e).
  Definition ti_pc21 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x22).
  Definition ti_pc22 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x26).
  Definition ti_pc23 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x2a).
  Definition ti_pc24 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x2e).
  Definition ti_pc25 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x30).
  Definition ti_pc26 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x34).
  Definition ti_pc27 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x36).
  Definition ti_pc28 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x38).
  Definition ti_pc29 : mword 64 := mword_of_int (KernelSyms.timerinit + 0x3a).

  (* ---- constructor templates (side conditions all vm_compute) ---- *)

  (* 4-aligned RVC: 4-byte window word [w], low 16 bits = the encoding [h]. *)
  (* 2-aligned (not 4-aligned) RVC: 2-byte window of the halfword [h]. *)
  (* 32-bit F_Base at any 2-aligned pc. *)
  Lemma ti_instr9 :
    kernel_text -∗ instr ti_pc9 true (ITYPE (sign_extend' 12 i9, Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.timerinit) ti_h9 ti_pc9 (ITYPE (sign_extend' 12 i9, Regidx csp_rs1, Regidx csp_rs1, ADDI)) ti_decode9 exec_execute_C_ADDI. Qed.

  Lemma ti_instr10 :
    kernel_text -∗ instr ti_pc10 true (STORE (zero_extend' 12 (concat_vec u10 ('b"000")), Regidx ti_ra, Regidx csp_rs1, 8)).
  Proof. mk_rvc (KernelSyms.timerinit + 0x2) ti_h10 ti_pc10 (STORE (zero_extend' 12 (concat_vec u10 ('b"000")), Regidx ti_ra, Regidx csp_rs1, 8)) ti_decode10 exec_execute_C_SDSP. Qed.

  Lemma ti_instr11 :
    kernel_text -∗ instr ti_pc11 true (STORE (zero_extend' 12 (concat_vec u11 ('b"000")), Regidx ti_s0, Regidx csp_rs1, 8)).
  Proof. mk_rvc (KernelSyms.timerinit + 0x4) ti_h11 ti_pc11 (STORE (zero_extend' 12 (concat_vec u11 ('b"000")), Regidx ti_s0, Regidx csp_rs1, 8)) ti_decode11 exec_execute_C_SDSP. Qed.

  Lemma ti_instr12 :
    kernel_text -∗ instr ti_pc12 true (ITYPE (caddi4spn_imm nz12, Regidx csp_rs1, Regidx ti_s0, ADDI)).
  Proof. mk_rvc (KernelSyms.timerinit + 0x6) ti_h12 ti_pc12 (ITYPE (caddi4spn_imm nz12, Regidx csp_rs1, Regidx ti_s0, ADDI)) ti_decode12 exec_execute_C_ADDI4SPN. Qed.

  Lemma ti_instr13 :
    kernel_text -∗ instr ti_pc13 false (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS)).
  Proof. mk_base (KernelSyms.timerinit + 0x8) ti_w13 ti_pc13 (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS)) ti_decode13. Qed.

  Lemma ti_instr14 :
    kernel_text -∗ instr ti_pc14 true (ITYPE (sign_extend' 12 i14, Regidx cli_rs1, Regidx ti_a4, ADDI)).
  Proof. mk_rvc (KernelSyms.timerinit + 0xc) ti_h14 ti_pc14 (ITYPE (sign_extend' 12 i14, Regidx cli_rs1, Regidx ti_a4, ADDI)) ti_decode14 exec_execute_C_LI. Qed.

  Lemma ti_instr15 :
    kernel_text -∗ instr ti_pc15 true (SHIFTIOP (sh15, Regidx ti_a4, Regidx ti_a4, SLLI)).
  Proof. mk_rvc (KernelSyms.timerinit + 0xe) ti_h15 ti_pc15 (SHIFTIOP (sh15, Regidx ti_a4, Regidx ti_a4, SLLI)) ti_decode15 exec_execute_C_SLLI. Qed.

  Lemma ti_instr16 :
    kernel_text -∗ instr ti_pc16 true (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)).
  Proof. mk_rvc (KernelSyms.timerinit + 0x10) ti_h16 ti_pc16 (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)) ti_decode16 exec_execute_C_OR. Qed.

  Lemma ti_instr17 :
    kernel_text -∗ instr ti_pc17 false (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW)).
  Proof. mk_base (KernelSyms.timerinit + 0x12) ti_w17 ti_pc17 (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW)) ti_decode17. Qed.

  Lemma ti_instr18 :
    kernel_text -∗ instr ti_pc18 false (CSRReg (WpGprCsrrA.csr_mcounteren, zreg, Regidx ti_a5, CSRRS)).
  Proof. mk_base (KernelSyms.timerinit + 0x16) ti_w18 ti_pc18 (CSRReg (WpGprCsrrA.csr_mcounteren, zreg, Regidx ti_a5, CSRRS)) ti_decode18. Qed.

  Lemma ti_instr19 :
    kernel_text -∗ instr ti_pc19 false (ITYPE (i19, Regidx ti_a5, Regidx ti_a5, ORI)).
  Proof. mk_base (KernelSyms.timerinit + 0x1a) ti_w19 ti_pc19 (ITYPE (i19, Regidx ti_a5, Regidx ti_a5, ORI)) ti_decode19. Qed.

  Lemma ti_instr20 :
    kernel_text -∗ instr ti_pc20 false (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx ti_a5, zreg, CSRRW)).
  Proof. mk_base (KernelSyms.timerinit + 0x1e) ti_w20 ti_pc20 (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx ti_a5, zreg, CSRRW)) ti_decode20. Qed.

  Lemma ti_instr21 :
    kernel_text -∗ instr ti_pc21 false (CSRReg (WpGprCsrrB.csr_time, zreg, Regidx ti_a5, CSRRS)).
  Proof. mk_base (KernelSyms.timerinit + 0x22) ti_w21 ti_pc21 (CSRReg (WpGprCsrrB.csr_time, zreg, Regidx ti_a5, CSRRS)) ti_decode21. Qed.

  Lemma ti_instr22 :
    kernel_text -∗ instr ti_pc22 false (UTYPE (i22, Regidx ti_a4, LUI)).
  Proof. mk_base (KernelSyms.timerinit + 0x26) ti_w22 ti_pc22 (UTYPE (i22, Regidx ti_a4, LUI)) ti_decode22. Qed.

  Lemma ti_instr23 :
    kernel_text -∗ instr ti_pc23 false (ITYPE (i23, Regidx ti_a4, Regidx ti_a4, ADDI)).
  Proof. mk_base (KernelSyms.timerinit + 0x2a) ti_w23 ti_pc23 (ITYPE (i23, Regidx ti_a4, Regidx ti_a4, ADDI)) ti_decode23. Qed.

  Lemma ti_instr24 :
    kernel_text -∗ instr ti_pc24 true (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, ADD)).
  Proof. mk_rvc (KernelSyms.timerinit + 0x2e) ti_h24 ti_pc24 (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, ADD)) ti_decode24 exec_execute_C_ADD. Qed.

  Lemma ti_instr25 :
    kernel_text -∗ instr ti_pc25 false (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx ti_a5, zreg, CSRRW)).
  Proof. mk_base (KernelSyms.timerinit + 0x30) ti_w25 ti_pc25 (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx ti_a5, zreg, CSRRW)) ti_decode25. Qed.

  Lemma ti_instr26 :
    kernel_text -∗ instr ti_pc26 true (LOAD (zero_extend' 12 (concat_vec u10 ('b"000")), Regidx csp_rs1, Regidx ti_ra, false, 8)).
  Proof. mk_rvc (KernelSyms.timerinit + 0x34) ti_h26 ti_pc26 (LOAD (zero_extend' 12 (concat_vec u10 ('b"000")), Regidx csp_rs1, Regidx ti_ra, false, 8)) ti_decode26 exec_execute_C_LDSP. Qed.

  Lemma ti_instr27 :
    kernel_text -∗ instr ti_pc27 true (LOAD (zero_extend' 12 (concat_vec u11 ('b"000")), Regidx csp_rs1, Regidx ti_s0, false, 8)).
  Proof. mk_rvc (KernelSyms.timerinit + 0x36) ti_h27 ti_pc27 (LOAD (zero_extend' 12 (concat_vec u11 ('b"000")), Regidx csp_rs1, Regidx ti_s0, false, 8)) ti_decode27 exec_execute_C_LDSP. Qed.

  Lemma ti_instr28 :
    kernel_text -∗ instr ti_pc28 true (ITYPE (sign_extend' 12 i28, Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.timerinit + 0x38) ti_h28 ti_pc28 (ITYPE (sign_extend' 12 i28, Regidx csp_rs1, Regidx csp_rs1, ADDI)) ti_decode28 exec_execute_C_ADDI. Qed.

  Lemma ti_instr29 :
    kernel_text -∗ instr ti_pc29 true (JALR (zeros' 12, Regidx ti_ra, zreg)).
  Proof. mk_rvc (KernelSyms.timerinit + 0x3a) ti_h29 ti_pc29 (JALR (zeros' 12, Regidx ti_ra, zreg)) ti_decode29 exec_execute_C_JR. Qed.

End WpTimerinit.
