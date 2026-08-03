(* CodeStart.v -- the machine code of start(): the decode templates for the
   words this function alone uses, and the [instr] constructors for its
   instruction addresses.  Consumed by WpStartNew.v. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import StackOwn.
Require Import RegFile.
Require Import WpGprCsrwCommon.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpDecode ExecCommon WpGpr.
Require Import WpAuipc WpMmodeShiftiop WpMmodeJal.
Require Import WpMmodeLeafBase.
Require Import WpMmodeUtype.
Require Import WpMmodeAddiw.
Require Import WpMmodeItype.
Require Import WpMmodeRtype.
Require Import WpMmodeStore.
Require Import WpGprCsrrA WpGprCsrrB WpGprCsrwA WpGprCsrwB WpGprCsrwC.
Require Import WpGprMretWp.
Require Import WpMmodeLeafBase.
Require Import WpMmodeMret.
Require Import InstrBytes KernelText WpTimerinit CodeTimerinit.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.


(* ===================================================================== *)
(* Canonical operand values.  The register / small-immediate literals    *)
(* i9 / u10 / u11 / nz12 / ti_ra / ti_s0 / ti_a4 / ti_a5 / ti_ca4 /      *)
(* ti_ca5 are REUSED from WpTimerinit (same registers, same encodings).  *)
(* ===================================================================== *)
Definition st_tp : mword 5 := mword_of_int 4.    (* x4 *)

Definition si35 : mword 6  := mword_of_int 62.    (* c.lui a4, imm6 (-2 -> 0xffffe) *)
Definition si36 : mword 12 := mword_of_int 2047.  (* addi a4, 2047 *)
Definition si38 : mword 6  := mword_of_int 1.     (* c.lui a4, 1 *)
Definition si39 : mword 12 := mword_of_int 2048.  (* addi a4, -2048 (bits 0x800) *)
Definition si42 : mword 20 := mword_of_int 1.     (* auipc a5, 1 *)
Definition si43 : mword 12 := mword_of_int 3590.  (* addi a5, -506 (bits 0xe06) *)
Definition si45 : mword 6  := mword_of_int 0.     (* c.li a5, 0 *)
Definition si47 : mword 6  := mword_of_int 16.    (* c.lui a5, 0x10 *)
Definition si48 : mword 6  := mword_of_int 63.    (* c.addi a5, -1 *)
Definition si52 : mword 12 := mword_of_int 544.   (* ori a5, 544 *)
Definition si54 : mword 6  := mword_of_int 63.    (* c.li a5, -1 *)
Definition ssh55 : mword 6 := mword_of_int 10.    (* c.srli a5, 0xa *)
Definition si57 : mword 6  := mword_of_int 15.    (* c.li a5, 15 *)
Definition sjimm59 : mword 21 := mword_of_int 0x1fff5e. (* jal offset -162 *)
Definition si61 : mword 6  := mword_of_int 0.     (* c.addiw a5, 0 *)
(* the ADUE menvcfg-write block (start+0x58..0x62): [menvcfg |= 1<<61]. *)
Definition sae_li   : mword 6 := mword_of_int 1.  (* c.li   a4, 1     *)
Definition sae_slli : mword 6 := mword_of_int 61. (* c.slli a4, 0x3d  *)

(* the RVC halfwords and, for the 4-aligned RVC sites, the whole 4-byte
   fetch-window words; halfwords already present in WpTimerinit are reused
   (ti_h9 = 0x1141, ti_h10 = 0xe406, ti_h11 = 0xe022, ti_h12 = 0x0800,
   ti_h16 = 0x8fd9). *)
Definition st_w34 : mword 32 := mword_of_int 0x300027f3.
Definition st_h35 : mword 16 := mword_of_int 0x7779.
Definition st_w36 : mword 32 := mword_of_int 0x7ff70713.
Definition st_h37 : mword 16 := mword_of_int 0x8ff9.
Definition st_h38 : mword 16 := mword_of_int 0x6705.
Definition st_w39 : mword 32 := mword_of_int 0x80070713.
Definition st_w41 : mword 32 := mword_of_int 0x30079073.
Definition st_w42 : mword 32 := mword_of_int 0x00001797.
Definition st_w43 : mword 32 := mword_of_int 0xe0678793.
Definition st_w44 : mword 32 := mword_of_int 0x34179073.
Definition st_h45 : mword 16 := mword_of_int 0x4781.
Definition st_w46 : mword 32 := mword_of_int 0x18079073.
Definition st_h47 : mword 16 := mword_of_int 0x67c1.
Definition st_h48 : mword 16 := mword_of_int 0x17fd.
Definition st_w49 : mword 32 := mword_of_int 0x30279073.
Definition st_w50 : mword 32 := mword_of_int 0x30379073.
Definition st_w51 : mword 32 := mword_of_int 0x104027f3.
Definition st_w52 : mword 32 := mword_of_int 0x2207e793.
Definition st_w53 : mword 32 := mword_of_int 0x10479073.
Definition st_h54 : mword 16 := mword_of_int 0x57fd.
Definition st_h55 : mword 16 := mword_of_int 0x83a9.
Definition st_w56 : mword 32 := mword_of_int 0x3b079073.
Definition st_h57 : mword 16 := mword_of_int 0x47bd.
Definition st_w58 : mword 32 := mword_of_int 0x3a079073.
Definition st_w59 : mword 32 := mword_of_int 0xf5fff0ef.
Definition st_w60 : mword 32 := mword_of_int 0xf14027f3.
Definition st_h61 : mword 16 := mword_of_int 0x2781.
(* ADUE block halfwords (csrr/csrw reuse ti_w13/ti_w17; c.or reuses ti_h16). *)
Definition st_h_aeli   : mword 16 := mword_of_int 0x4705.  (* c.li   a4, 1    *)
Definition st_h_aeslli : mword 16 := mword_of_int 0x1776.  (* c.slli a4, 0x3d *)
Definition st_h62 : mword 16 := mword_of_int 0x823e.
(* MRET's word is WpGprMretWp.w_mret (0x30200073). *)

(* ===================================================================== *)
(* Decode lemmas for the encodings not already decoded by WpTimerinit /  *)
(* WpEntry / WpGprMretWp.  RVC: the WpEntry clause walkers + per-clause   *)
(* closes (WpTimerinit recipe); 32-bit: [decode_any] one-shot.            *)
(* ===================================================================== *)

Local Ltac st_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

(* single [and_boolM (returnM _) (currentlyEnabled Ext_Zca)] guard *)
Local Ltac st_close1 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; st_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

(* double-nested [and_boolM (returnM _) (and_boolM (returnM _) (cE Zca))] *)
Local Ltac st_close2 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (Defs.and_boolM (returnM _)
                          (currentlyEnabled Ext_Zca))) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; st_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

(* bare [currentlyEnabled Ext_Zca] guard *)
Local Ltac st_close0 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; st_ast
  | apply (exec_currentlyEnabled_Zca s HmisaC) ].

(* ---- idx 35: 0x7779 -> c.lui a4, 62(=0xffffe) ---- *)
Lemma st_decode35 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed st_h35) s = Some (C_LUI (si35, Regidx ti_a4), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 37: 0x8ff9 -> c.and a5, a4 ---- *)
Lemma st_decode37 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed st_h37) s = Some (C_AND (ti_ca5, ti_ca4), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 38: 0x6705 -> c.lui a4, 1 ---- *)
Lemma st_decode38 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed st_h38) s = Some (C_LUI (si38, Regidx ti_a4), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 45: 0x4781 -> c.li a5, 0 ---- *)
Lemma st_decode45 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed st_h45) s = Some (C_LI (si45, Regidx ti_a5), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 47: 0x67c1 -> c.lui a5, 16 ---- *)
Lemma st_decode47 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed st_h47) s = Some (C_LUI (si47, Regidx ti_a5), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 48: 0x17fd -> c.addi a5, -1 ---- *)
Lemma st_decode48 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed st_h48) s = Some (C_ADDI (si48, Regidx ti_a5), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 54: 0x57fd -> c.li a5, -1 ---- *)
Lemma st_decode54 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed st_h54) s = Some (C_LI (si54, Regidx ti_a5), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 55: 0x83a9 -> c.srli a5, 10 ---- *)
Lemma st_decode55 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed st_h55) s = Some (C_SRLI (ssh55, ti_ca5), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 57: 0x47bd -> c.li a5, 15 ---- *)
Lemma st_decode57 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed st_h57) s = Some (C_LI (si57, Regidx ti_a5), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 61: 0x2781 -> c.addiw a5, 0 ---- *)
(* The C_JAL / C_ADDIW encodings share one fused decoder clause, guarded by
   [and_boolM (and_boolM (returnM (xlen =? 32)) (cE Zca)) (returnM pat)]: on
   RV64 the C_JAL side collapses to false (xlen <> 32, short-circuiting past
   the Zca read), selecting the C_ADDIW body. *)
Lemma st_decode61 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed st_h61) s = Some (C_ADDIW (si61, Regidx ti_a5), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ---- idx 62: 0x823e -> c.mv tp, a5 ---- *)
Lemma st_decode62 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed st_h62) s = Some (C_MV (Regidx st_tp, Regidx ti_a5), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ADUE block: c.li a4,1 (0x4705) and c.slli a4,0x3d (0x1776). *)
Lemma st_decode_aeli s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed st_h_aeli) s = Some (C_LI (sae_li, Regidx ti_a4), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma st_decode_aeslli s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed st_h_aeslli) s = Some (C_SLLI (sae_slli, Regidx ti_a4), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

(* ---- the sixteen 32-bit instructions: one-shot [decode_any] ---- *)
Lemma st_decode34 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w34) s
    = Some (CSRReg (WpGprCsrrA.csr_mstatus, zreg, Regidx ti_a5, CSRRS), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode36 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w36) s
    = Some (ITYPE (si36, Regidx ti_a4, Regidx ti_a4, ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode39 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w39) s
    = Some (ITYPE (si39, Regidx ti_a4, Regidx ti_a4, ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode41 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w41) s
    = Some (CSRReg (WpGprCsrwA.csr_mstatus, Regidx ti_a5, zreg, CSRRW), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode42 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w42) s
    = Some (UTYPE (si42, Regidx ti_a5, AUIPC), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode43 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w43) s
    = Some (ITYPE (si43, Regidx ti_a5, Regidx ti_a5, ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode44 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w44) s
    = Some (CSRReg (WpGprCsrwA.csr_mepc, Regidx ti_a5, zreg, CSRRW), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode46 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w46) s
    = Some (CSRReg (WpGprCsrwB.csr_satp, Regidx ti_a5, zreg, CSRRW), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode49 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w49) s
    = Some (CSRReg (WpGprCsrwA.csr_medeleg, Regidx ti_a5, zreg, CSRRW), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode50 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w50) s
    = Some (CSRReg (WpGprCsrwB.csr_mideleg, Regidx ti_a5, zreg, CSRRW), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode51 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w51) s
    = Some (CSRReg (WpGprCsrrB.csr_sie, zreg, Regidx ti_a5, CSRRS), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode52 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w52) s
    = Some (ITYPE (si52, Regidx ti_a5, Regidx ti_a5, ORI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode53 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w53) s
    = Some (CSRReg (WpGprCsrwB.csr_sie, Regidx ti_a5, zreg, CSRRW), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode56 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w56) s
    = Some (CSRReg (WpGprCsrwB.csr_pmpaddr0, Regidx ti_a5, zreg, CSRRW), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode58 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w58) s
    = Some (CSRReg (WpGprCsrwA.csr_pmpcfg0, Regidx ti_a5, zreg, CSRRW), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode59 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w59) s
    = Some (JAL (sjimm59, Regidx ti_ra), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma st_decode60 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode st_w60) s
    = Some (CSRReg (ExecCommon.csr_csrr, zreg, Regidx ti_a5, CSRRS), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* idx 63 MRET: [decode_mret] (WpGprMretWp) applies verbatim (w_mret is the
   same word 0x30200073). *)

(* ===================================================================== *)
(* The 34 [instr] constructors from [kernel_text] (WpEntryNew recipe).    *)
(* ===================================================================== *)
(* discharge [wp_instr]'s per-byte static premise at a concrete boot pc. *)
Ltac boot_static :=
  apply KptPt.instr_window_static; intros jj Hjj; unfold addr_is_text;
  destruct jj as [|[|[|[|]]]]; try lia;
  (split; [vm_compute; discriminate | vm_compute; reflexivity]).

Section WpStartInstr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* PCs of the 34 instructions. *)
  Definition st_pc30 : mword 64 := mword_of_int (KernelSyms.start).
  Definition st_pc31 : mword 64 := mword_of_int (KernelSyms.start + 0x2).
  Definition st_pc32 : mword 64 := mword_of_int (KernelSyms.start + 0x4).
  Definition st_pc33 : mword 64 := mword_of_int (KernelSyms.start + 0x6).
  Definition st_pc34 : mword 64 := mword_of_int (KernelSyms.start + 0x8).
  Definition st_pc35 : mword 64 := mword_of_int (KernelSyms.start + 0xc).
  Definition st_pc36 : mword 64 := mword_of_int (KernelSyms.start + 0xe).
  Definition st_pc37 : mword 64 := mword_of_int (KernelSyms.start + 0x12).
  Definition st_pc38 : mword 64 := mword_of_int (KernelSyms.start + 0x14).
  Definition st_pc39 : mword 64 := mword_of_int (KernelSyms.start + 0x16).
  Definition st_pc40 : mword 64 := mword_of_int (KernelSyms.start + 0x1a).
  Definition st_pc41 : mword 64 := mword_of_int (KernelSyms.start + 0x1c).
  Definition st_pc42 : mword 64 := mword_of_int (KernelSyms.start + 0x20).
  Definition st_pc43 : mword 64 := mword_of_int (KernelSyms.start + 0x24).
  Definition st_pc44 : mword 64 := mword_of_int (KernelSyms.start + 0x28).
  Definition st_pc45 : mword 64 := mword_of_int (KernelSyms.start + 0x2c).
  Definition st_pc46 : mword 64 := mword_of_int (KernelSyms.start + 0x2e).
  Definition st_pc47 : mword 64 := mword_of_int (KernelSyms.start + 0x32).
  Definition st_pc48 : mword 64 := mword_of_int (KernelSyms.start + 0x34).
  Definition st_pc49 : mword 64 := mword_of_int (KernelSyms.start + 0x36).
  Definition st_pc50 : mword 64 := mword_of_int (KernelSyms.start + 0x3a).
  Definition st_pc51 : mword 64 := mword_of_int (KernelSyms.start + 0x3e).
  Definition st_pc52 : mword 64 := mword_of_int (KernelSyms.start + 0x42).
  Definition st_pc53 : mword 64 := mword_of_int (KernelSyms.start + 0x46).
  Definition st_pc54 : mword 64 := mword_of_int (KernelSyms.start + 0x4a).
  Definition st_pc55 : mword 64 := mword_of_int (KernelSyms.start + 0x4c).
  Definition st_pc56 : mword 64 := mword_of_int (KernelSyms.start + 0x4e).
  Definition st_pc57 : mword 64 := mword_of_int (KernelSyms.start + 0x52).
  Definition st_pc58 : mword 64 := mword_of_int (KernelSyms.start + 0x54).
  (* ADUE menvcfg-write block (indices between pmpcfg0 and the timerinit jal). *)
  Definition st_pc_ae0 : mword 64 := mword_of_int (KernelSyms.start + 0x58). (* csrr  a5,menvcfg *)
  Definition st_pc_ae1 : mword 64 := mword_of_int (KernelSyms.start + 0x5c). (* c.li  a4,1       *)
  Definition st_pc_ae2 : mword 64 := mword_of_int (KernelSyms.start + 0x5e). (* c.slli a4,0x3d   *)
  Definition st_pc_ae3 : mword 64 := mword_of_int (KernelSyms.start + 0x60). (* c.or  a5,a4      *)
  Definition st_pc_ae4 : mword 64 := mword_of_int (KernelSyms.start + 0x62). (* csrw  menvcfg,a5 *)
  Definition st_pc59 : mword 64 := mword_of_int (KernelSyms.start + 0x66). (* jal timerinit   *)
  Definition st_pc60 : mword 64 := mword_of_int (KernelSyms.start + 0x6a). (* csrr a5,mhartid *)
  Definition st_pc61 : mword 64 := mword_of_int (KernelSyms.start + 0x6e). (* c.addiw a5,0    *)
  Definition st_pc62 : mword 64 := mword_of_int (KernelSyms.start + 0x70). (* c.mv tp,a5      *)
  Definition st_pc63 : mword 64 := mword_of_int (KernelSyms.start + 0x72). (* mret           *)

  (* ---- constructor templates (copied from WpTimerinit; file-local) ---- *)
  Lemma st_instr30 :
    kernel_text -∗ instr st_pc30 true (ITYPE (sign_extend' 12 i9, Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.start) ti_h9 st_pc30 (ITYPE (sign_extend' 12 i9, Regidx csp_rs1, Regidx csp_rs1, ADDI)) ti_decode9 exec_execute_C_ADDI. Qed.

  Lemma st_instr31 :
    kernel_text -∗ instr st_pc31 true (STORE (zero_extend' 12 (concat_vec u10 ('b"000")), Regidx ti_ra, Regidx csp_rs1, 8)).
  Proof. mk_rvc (KernelSyms.start + 0x2) ti_h10 st_pc31 (STORE (zero_extend' 12 (concat_vec u10 ('b"000")), Regidx ti_ra, Regidx csp_rs1, 8)) ti_decode10 exec_execute_C_SDSP. Qed.

  Lemma st_instr32 :
    kernel_text -∗ instr st_pc32 true (STORE (zero_extend' 12 (concat_vec u11 ('b"000")), Regidx ti_s0, Regidx csp_rs1, 8)).
  Proof. mk_rvc (KernelSyms.start + 0x4) ti_h11 st_pc32 (STORE (zero_extend' 12 (concat_vec u11 ('b"000")), Regidx ti_s0, Regidx csp_rs1, 8)) ti_decode11 exec_execute_C_SDSP. Qed.

  Lemma st_instr33 :
    kernel_text -∗ instr st_pc33 true (ITYPE (caddi4spn_imm nz12, Regidx csp_rs1, Regidx ti_s0, ADDI)).
  Proof. mk_rvc (KernelSyms.start + 0x6) ti_h12 st_pc33 (ITYPE (caddi4spn_imm nz12, Regidx csp_rs1, Regidx ti_s0, ADDI)) ti_decode12 exec_execute_C_ADDI4SPN. Qed.

  Lemma st_instr34 :
    kernel_text -∗ instr st_pc34 false (CSRReg (WpGprCsrrA.csr_mstatus, zreg, Regidx ti_a5, CSRRS)).
  Proof. mk_base (KernelSyms.start + 0x8) st_w34 st_pc34 (CSRReg (WpGprCsrrA.csr_mstatus, zreg, Regidx ti_a5, CSRRS)) st_decode34. Qed.

  Lemma st_instr35 :
    kernel_text -∗ instr st_pc35 true (UTYPE (sign_extend' 20 si35, Regidx ti_a4, LUI)).
  Proof. mk_rvc (KernelSyms.start + 0xc) st_h35 st_pc35 (UTYPE (sign_extend' 20 si35, Regidx ti_a4, LUI)) st_decode35 exec_execute_C_LUI. Qed.

  Lemma st_instr36 :
    kernel_text -∗ instr st_pc36 false (ITYPE (si36, Regidx ti_a4, Regidx ti_a4, ADDI)).
  Proof. mk_base (KernelSyms.start + 0xe) st_w36 st_pc36 (ITYPE (si36, Regidx ti_a4, Regidx ti_a4, ADDI)) st_decode36. Qed.

  Lemma st_instr37 :
    kernel_text -∗ instr st_pc37 true (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, AND)).
  Proof. mk_rvc (KernelSyms.start + 0x12) st_h37 st_pc37 (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, AND)) st_decode37 exec_execute_C_AND. Qed.

  Lemma st_instr38 :
    kernel_text -∗ instr st_pc38 true (UTYPE (sign_extend' 20 si38, Regidx ti_a4, LUI)).
  Proof. mk_rvc (KernelSyms.start + 0x14) st_h38 st_pc38 (UTYPE (sign_extend' 20 si38, Regidx ti_a4, LUI)) st_decode38 exec_execute_C_LUI. Qed.

  Lemma st_instr39 :
    kernel_text -∗ instr st_pc39 false (ITYPE (si39, Regidx ti_a4, Regidx ti_a4, ADDI)).
  Proof. mk_base (KernelSyms.start + 0x16) st_w39 st_pc39 (ITYPE (si39, Regidx ti_a4, Regidx ti_a4, ADDI)) st_decode39. Qed.

  Lemma st_instr40 :
    kernel_text -∗ instr st_pc40 true (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)).
  Proof. mk_rvc (KernelSyms.start + 0x1a) ti_h16 st_pc40 (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)) ti_decode16 exec_execute_C_OR. Qed.

  Lemma st_instr41 :
    kernel_text -∗ instr st_pc41 false (CSRReg (WpGprCsrwA.csr_mstatus, Regidx ti_a5, zreg, CSRRW)).
  Proof. mk_base (KernelSyms.start + 0x1c) st_w41 st_pc41 (CSRReg (WpGprCsrwA.csr_mstatus, Regidx ti_a5, zreg, CSRRW)) st_decode41. Qed.

  Lemma st_instr42 :
    kernel_text -∗ instr st_pc42 false (UTYPE (si42, Regidx ti_a5, AUIPC)).
  Proof. mk_base (KernelSyms.start + 0x20) st_w42 st_pc42 (UTYPE (si42, Regidx ti_a5, AUIPC)) st_decode42. Qed.

  Lemma st_instr43 :
    kernel_text -∗ instr st_pc43 false (ITYPE (si43, Regidx ti_a5, Regidx ti_a5, ADDI)).
  Proof. mk_base (KernelSyms.start + 0x24) st_w43 st_pc43 (ITYPE (si43, Regidx ti_a5, Regidx ti_a5, ADDI)) st_decode43. Qed.

  Lemma st_instr44 :
    kernel_text -∗ instr st_pc44 false (CSRReg (WpGprCsrwA.csr_mepc, Regidx ti_a5, zreg, CSRRW)).
  Proof. mk_base (KernelSyms.start + 0x28) st_w44 st_pc44 (CSRReg (WpGprCsrwA.csr_mepc, Regidx ti_a5, zreg, CSRRW)) st_decode44. Qed.

  Lemma st_instr45 :
    kernel_text -∗ instr st_pc45 true (ITYPE (sign_extend' 12 si45, Regidx cli_rs1, Regidx ti_a5, ADDI)).
  Proof. mk_rvc (KernelSyms.start + 0x2c) st_h45 st_pc45 (ITYPE (sign_extend' 12 si45, Regidx cli_rs1, Regidx ti_a5, ADDI)) st_decode45 exec_execute_C_LI. Qed.

  Lemma st_instr46 :
    kernel_text -∗ instr st_pc46 false (CSRReg (WpGprCsrwB.csr_satp, Regidx ti_a5, zreg, CSRRW)).
  Proof. mk_base (KernelSyms.start + 0x2e) st_w46 st_pc46 (CSRReg (WpGprCsrwB.csr_satp, Regidx ti_a5, zreg, CSRRW)) st_decode46. Qed.

  Lemma st_instr47 :
    kernel_text -∗ instr st_pc47 true (UTYPE (sign_extend' 20 si47, Regidx ti_a5, LUI)).
  Proof. mk_rvc (KernelSyms.start + 0x32) st_h47 st_pc47 (UTYPE (sign_extend' 20 si47, Regidx ti_a5, LUI)) st_decode47 exec_execute_C_LUI. Qed.

  Lemma st_instr48 :
    kernel_text -∗ instr st_pc48 true (ITYPE (sign_extend' 12 si48, Regidx ti_a5, Regidx ti_a5, ADDI)).
  Proof. mk_rvc (KernelSyms.start + 0x34) st_h48 st_pc48 (ITYPE (sign_extend' 12 si48, Regidx ti_a5, Regidx ti_a5, ADDI)) st_decode48 exec_execute_C_ADDI. Qed.

  Lemma st_instr49 :
    kernel_text -∗ instr st_pc49 false (CSRReg (WpGprCsrwA.csr_medeleg, Regidx ti_a5, zreg, CSRRW)).
  Proof. mk_base (KernelSyms.start + 0x36) st_w49 st_pc49 (CSRReg (WpGprCsrwA.csr_medeleg, Regidx ti_a5, zreg, CSRRW)) st_decode49. Qed.

  Lemma st_instr50 :
    kernel_text -∗ instr st_pc50 false (CSRReg (WpGprCsrwB.csr_mideleg, Regidx ti_a5, zreg, CSRRW)).
  Proof. mk_base (KernelSyms.start + 0x3a) st_w50 st_pc50 (CSRReg (WpGprCsrwB.csr_mideleg, Regidx ti_a5, zreg, CSRRW)) st_decode50. Qed.

  Lemma st_instr51 :
    kernel_text -∗ instr st_pc51 false (CSRReg (WpGprCsrrB.csr_sie, zreg, Regidx ti_a5, CSRRS)).
  Proof. mk_base (KernelSyms.start + 0x3e) st_w51 st_pc51 (CSRReg (WpGprCsrrB.csr_sie, zreg, Regidx ti_a5, CSRRS)) st_decode51. Qed.

  Lemma st_instr52 :
    kernel_text -∗ instr st_pc52 false (ITYPE (si52, Regidx ti_a5, Regidx ti_a5, ORI)).
  Proof. mk_base (KernelSyms.start + 0x42) st_w52 st_pc52 (ITYPE (si52, Regidx ti_a5, Regidx ti_a5, ORI)) st_decode52. Qed.

  Lemma st_instr53 :
    kernel_text -∗ instr st_pc53 false (CSRReg (WpGprCsrwB.csr_sie, Regidx ti_a5, zreg, CSRRW)).
  Proof. mk_base (KernelSyms.start + 0x46) st_w53 st_pc53 (CSRReg (WpGprCsrwB.csr_sie, Regidx ti_a5, zreg, CSRRW)) st_decode53. Qed.

  Lemma st_instr54 :
    kernel_text -∗ instr st_pc54 true (ITYPE (sign_extend' 12 si54, Regidx cli_rs1, Regidx ti_a5, ADDI)).
  Proof. mk_rvc (KernelSyms.start + 0x4a) st_h54 st_pc54 (ITYPE (sign_extend' 12 si54, Regidx cli_rs1, Regidx ti_a5, ADDI)) st_decode54 exec_execute_C_LI. Qed.

  Lemma st_instr55 :
    kernel_text -∗ instr st_pc55 true (SHIFTIOP (ssh55, Regidx ti_a5, Regidx ti_a5, SRLI)).
  Proof. mk_rvc (KernelSyms.start + 0x4c) st_h55 st_pc55 (SHIFTIOP (ssh55, Regidx ti_a5, Regidx ti_a5, SRLI)) st_decode55 exec_execute_C_SRLI. Qed.

  Lemma st_instr56 :
    kernel_text -∗ instr st_pc56 false (CSRReg (WpGprCsrwB.csr_pmpaddr0, Regidx ti_a5, zreg, CSRRW)).
  Proof. mk_base (KernelSyms.start + 0x4e) st_w56 st_pc56 (CSRReg (WpGprCsrwB.csr_pmpaddr0, Regidx ti_a5, zreg, CSRRW)) st_decode56. Qed.

  Lemma st_instr57 :
    kernel_text -∗ instr st_pc57 true (ITYPE (sign_extend' 12 si57, Regidx cli_rs1, Regidx ti_a5, ADDI)).
  Proof. mk_rvc (KernelSyms.start + 0x52) st_h57 st_pc57 (ITYPE (sign_extend' 12 si57, Regidx cli_rs1, Regidx ti_a5, ADDI)) st_decode57 exec_execute_C_LI. Qed.

  Lemma st_instr58 :
    kernel_text -∗ instr st_pc58 false (CSRReg (WpGprCsrwA.csr_pmpcfg0, Regidx ti_a5, zreg, CSRRW)).
  Proof. mk_base (KernelSyms.start + 0x54) st_w58 st_pc58 (CSRReg (WpGprCsrwA.csr_pmpcfg0, Regidx ti_a5, zreg, CSRRW)) st_decode58. Qed.

  (* ADUE menvcfg-write block: csrr/csrw menvcfg reuse WpTimerinit's decodes. *)
  Lemma st_instr_ae0 :
    kernel_text -∗ instr st_pc_ae0 false (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS)).
  Proof. mk_base (KernelSyms.start + 0x58) ti_w13 st_pc_ae0 (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS)) ti_decode13. Qed.

  Lemma st_instr_ae1 :
    kernel_text -∗ instr st_pc_ae1 true (ITYPE (sign_extend' 12 sae_li, Regidx cli_rs1, Regidx ti_a4, ADDI)).
  Proof. mk_rvc (KernelSyms.start + 0x5c) st_h_aeli st_pc_ae1 (ITYPE (sign_extend' 12 sae_li, Regidx cli_rs1, Regidx ti_a4, ADDI)) st_decode_aeli exec_execute_C_LI. Qed.

  Lemma st_instr_ae2 :
    kernel_text -∗ instr st_pc_ae2 true (SHIFTIOP (sae_slli, Regidx ti_a4, Regidx ti_a4, SLLI)).
  Proof. mk_rvc (KernelSyms.start + 0x5e) st_h_aeslli st_pc_ae2 (SHIFTIOP (sae_slli, Regidx ti_a4, Regidx ti_a4, SLLI)) st_decode_aeslli exec_execute_C_SLLI. Qed.

  Lemma st_instr_ae3 :
    kernel_text -∗ instr st_pc_ae3 true (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)).
  Proof. mk_rvc (KernelSyms.start + 0x60) ti_h16 st_pc_ae3 (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)) ti_decode16 exec_execute_C_OR. Qed.

  Lemma st_instr_ae4 :
    kernel_text -∗ instr st_pc_ae4 false (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW)).
  Proof. mk_base (KernelSyms.start + 0x62) ti_w17 st_pc_ae4 (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW)) ti_decode17. Qed.

  Lemma st_instr59 :
    kernel_text -∗ instr st_pc59 false (JAL (sjimm59, Regidx ti_ra)).
  Proof. mk_base (KernelSyms.start + 0x66) st_w59 st_pc59 (JAL (sjimm59, Regidx ti_ra)) st_decode59. Qed.

  Lemma st_instr60 :
    kernel_text -∗ instr st_pc60 false (CSRReg (ExecCommon.csr_csrr, zreg, Regidx ti_a5, CSRRS)).
  Proof. mk_base (KernelSyms.start + 0x6a) st_w60 st_pc60 (CSRReg (ExecCommon.csr_csrr, zreg, Regidx ti_a5, CSRRS)) st_decode60. Qed.

  Lemma st_instr61 :
    kernel_text -∗ instr st_pc61 true (ADDIW (sign_extend' 12 si61, Regidx ti_a5, Regidx ti_a5)).
  Proof. mk_rvc (KernelSyms.start + 0x6e) st_h61 st_pc61 (ADDIW (sign_extend' 12 si61, Regidx ti_a5, Regidx ti_a5)) st_decode61 exec_execute_C_ADDIW. Qed.

  Lemma st_instr62 :
    kernel_text -∗ instr st_pc62 true (RTYPE (Regidx ti_a5, Regidx cli_rs1, Regidx st_tp, ADD)).
  Proof. mk_rvc (KernelSyms.start + 0x70) st_h62 st_pc62 (RTYPE (Regidx ti_a5, Regidx cli_rs1, Regidx st_tp, ADD)) st_decode62 exec_execute_C_MV. Qed.

  Lemma st_instr63 :
    kernel_text -∗ instr st_pc63 false (MRET tt).
  Proof. mk_base (KernelSyms.start + 0x72) w_mret st_pc63 (MRET tt) decode_mret. Qed.

End WpStartInstr.
