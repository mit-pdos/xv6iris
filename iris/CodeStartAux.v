(* CodeStartAux.v -- start()'s operand vocabulary, over the GENERATED decode
   layer in CodeStart.v.

   The 39 [st_instr*] facts are conversions from their generated twins
   ([Proof. exact sti_<off>. Qed.]), so this file no longer carries a copy of
   any encoding word: the immediates and register indices below are what
   WpStartNew.v's weakest preconditions are written in, and the [exact] is a
   build-time check that they still match the dump.  See CodeEntryAux.v's
   header for the argument. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec ExecCommon.
Require Import WpGprCsrrA WpGprCsrrB WpGprCsrwA WpGprCsrwB.
Require Import WpMmodeLeafBase.
Require Import InstrBytes KernelText.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import CodeStart.
Require Import KernelConsts.
Require Import CodeTimerinitAux.
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
(* addi a5,a5,<imm> completing &main; read out of the image by
   tools/gen_consts.py, since it moves whenever main does *)
Definition si43 : mword 12 := mword_of_int KernelConsts.start_main_addi.
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
(* ADUE block halfwords (csrr/csrw reuse ti_w13/ti_w17; c.or reuses ti_h16). *)
(* MRET's word is WpGprMretWp.w_mret (0x30200073). *)

(* ===================================================================== *)
(* Decode lemmas for the encodings not already decoded by WpTimerinit /  *)
(* CodeEntry / WpGprMretWp.  RVC: CodeEntry's clause walkers + per-clause *)
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

(* ---- idx 37: 0x8ff9 -> c.and a5, a4 ---- *)

(* ---- idx 38: 0x6705 -> c.lui a4, 1 ---- *)

(* ---- idx 45: 0x4781 -> c.li a5, 0 ---- *)

(* ---- idx 47: 0x67c1 -> c.lui a5, 16 ---- *)

(* ---- idx 48: 0x17fd -> c.addi a5, -1 ---- *)

(* ---- idx 54: 0x57fd -> c.li a5, -1 ---- *)

(* ---- idx 55: 0x83a9 -> c.srli a5, 10 ---- *)

(* ---- idx 57: 0x47bd -> c.li a5, 15 ---- *)

(* ---- idx 61: 0x2781 -> c.addiw a5, 0 ---- *)
(* The C_JAL / C_ADDIW encodings share one fused decoder clause, guarded by
   [and_boolM (and_boolM (returnM (xlen =? 32)) (cE Zca)) (returnM pat)]: on
   RV64 the C_JAL side collapses to false (xlen <> 32, short-circuiting past
   the Zca read), selecting the C_ADDIW body. *)

(* ---- idx 62: 0x823e -> c.mv tp, a5 ---- *)

(* ADUE block: c.li a4,1 (0x4705) and c.slli a4,0x3d (0x1776). *)


(* ---- the sixteen 32-bit instructions: one-shot [decode_any] ---- *)

















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
  Context `{GEN : GenId} `{CID : CpuId}.

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
  Proof. exact sti_00. Qed.

  Lemma st_instr31 :
    kernel_text -∗ instr st_pc31 true (STORE (zero_extend' 12 (concat_vec u10 ('b"000")), Regidx ti_ra, Regidx csp_rs1, 8)).
  Proof. exact sti_02. Qed.

  Lemma st_instr32 :
    kernel_text -∗ instr st_pc32 true (STORE (zero_extend' 12 (concat_vec u11 ('b"000")), Regidx ti_s0, Regidx csp_rs1, 8)).
  Proof. exact sti_04. Qed.

  Lemma st_instr33 :
    kernel_text -∗ instr st_pc33 true (ITYPE (caddi4spn_imm nz12, Regidx csp_rs1, Regidx ti_s0, ADDI)).
  Proof. exact sti_06. Qed.

  Lemma st_instr34 :
    kernel_text -∗ instr st_pc34 false (CSRReg (WpGprCsrrA.csr_mstatus, zreg, Regidx ti_a5, CSRRS)).
  Proof. exact sti_08. Qed.

  Lemma st_instr35 :
    kernel_text -∗ instr st_pc35 true (UTYPE (sign_extend' 20 si35, Regidx ti_a4, LUI)).
  Proof. exact sti_0c. Qed.

  Lemma st_instr36 :
    kernel_text -∗ instr st_pc36 false (ITYPE (si36, Regidx ti_a4, Regidx ti_a4, ADDI)).
  Proof. exact sti_0e. Qed.

  Lemma st_instr37 :
    kernel_text -∗ instr st_pc37 true (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, AND)).
  Proof. exact sti_12. Qed.

  Lemma st_instr38 :
    kernel_text -∗ instr st_pc38 true (UTYPE (sign_extend' 20 si38, Regidx ti_a4, LUI)).
  Proof. exact sti_14. Qed.

  Lemma st_instr39 :
    kernel_text -∗ instr st_pc39 false (ITYPE (si39, Regidx ti_a4, Regidx ti_a4, ADDI)).
  Proof. exact sti_16. Qed.

  Lemma st_instr40 :
    kernel_text -∗ instr st_pc40 true (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)).
  Proof. exact sti_1a. Qed.

  Lemma st_instr41 :
    kernel_text -∗ instr st_pc41 false (CSRReg (WpGprCsrwA.csr_mstatus, Regidx ti_a5, zreg, CSRRW)).
  Proof. exact sti_1c. Qed.

  Lemma st_instr42 :
    kernel_text -∗ instr st_pc42 false (UTYPE (si42, Regidx ti_a5, AUIPC)).
  Proof. exact sti_20. Qed.

  Lemma st_instr43 :
    kernel_text -∗ instr st_pc43 false (ITYPE (si43, Regidx ti_a5, Regidx ti_a5, ADDI)).
  Proof. exact sti_24. Qed.

  Lemma st_instr44 :
    kernel_text -∗ instr st_pc44 false (CSRReg (WpGprCsrwA.csr_mepc, Regidx ti_a5, zreg, CSRRW)).
  Proof. exact sti_28. Qed.

  Lemma st_instr45 :
    kernel_text -∗ instr st_pc45 true (ITYPE (sign_extend' 12 si45, Regidx cli_rs1, Regidx ti_a5, ADDI)).
  Proof. exact sti_2c. Qed.

  Lemma st_instr46 :
    kernel_text -∗ instr st_pc46 false (CSRReg (WpGprCsrwB.csr_satp, Regidx ti_a5, zreg, CSRRW)).
  Proof. exact sti_2e. Qed.

  Lemma st_instr47 :
    kernel_text -∗ instr st_pc47 true (UTYPE (sign_extend' 20 si47, Regidx ti_a5, LUI)).
  Proof. exact sti_32. Qed.

  Lemma st_instr48 :
    kernel_text -∗ instr st_pc48 true (ITYPE (sign_extend' 12 si48, Regidx ti_a5, Regidx ti_a5, ADDI)).
  Proof. exact sti_34. Qed.

  Lemma st_instr49 :
    kernel_text -∗ instr st_pc49 false (CSRReg (WpGprCsrwA.csr_medeleg, Regidx ti_a5, zreg, CSRRW)).
  Proof. exact sti_36. Qed.

  Lemma st_instr50 :
    kernel_text -∗ instr st_pc50 false (CSRReg (WpGprCsrwB.csr_mideleg, Regidx ti_a5, zreg, CSRRW)).
  Proof. exact sti_3a. Qed.

  Lemma st_instr51 :
    kernel_text -∗ instr st_pc51 false (CSRReg (WpGprCsrrB.csr_sie, zreg, Regidx ti_a5, CSRRS)).
  Proof. exact sti_3e. Qed.

  Lemma st_instr52 :
    kernel_text -∗ instr st_pc52 false (ITYPE (si52, Regidx ti_a5, Regidx ti_a5, ORI)).
  Proof. exact sti_42. Qed.

  Lemma st_instr53 :
    kernel_text -∗ instr st_pc53 false (CSRReg (WpGprCsrwB.csr_sie, Regidx ti_a5, zreg, CSRRW)).
  Proof. exact sti_46. Qed.

  Lemma st_instr54 :
    kernel_text -∗ instr st_pc54 true (ITYPE (sign_extend' 12 si54, Regidx cli_rs1, Regidx ti_a5, ADDI)).
  Proof. exact sti_4a. Qed.

  Lemma st_instr55 :
    kernel_text -∗ instr st_pc55 true (SHIFTIOP (ssh55, Regidx ti_a5, Regidx ti_a5, SRLI)).
  Proof. exact sti_4c. Qed.

  Lemma st_instr56 :
    kernel_text -∗ instr st_pc56 false (CSRReg (WpGprCsrwB.csr_pmpaddr0, Regidx ti_a5, zreg, CSRRW)).
  Proof. exact sti_4e. Qed.

  Lemma st_instr57 :
    kernel_text -∗ instr st_pc57 true (ITYPE (sign_extend' 12 si57, Regidx cli_rs1, Regidx ti_a5, ADDI)).
  Proof. exact sti_52. Qed.

  Lemma st_instr58 :
    kernel_text -∗ instr st_pc58 false (CSRReg (WpGprCsrwA.csr_pmpcfg0, Regidx ti_a5, zreg, CSRRW)).
  Proof. exact sti_54. Qed.

  (* ADUE menvcfg-write block: csrr/csrw menvcfg reuse WpTimerinit's decodes. *)
  Lemma st_instr_ae0 :
    kernel_text -∗ instr st_pc_ae0 false (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS)).
  Proof. exact sti_58. Qed.

  Lemma st_instr_ae1 :
    kernel_text -∗ instr st_pc_ae1 true (ITYPE (sign_extend' 12 sae_li, Regidx cli_rs1, Regidx ti_a4, ADDI)).
  Proof. exact sti_5c. Qed.

  Lemma st_instr_ae2 :
    kernel_text -∗ instr st_pc_ae2 true (SHIFTIOP (sae_slli, Regidx ti_a4, Regidx ti_a4, SLLI)).
  Proof. exact sti_5e. Qed.

  Lemma st_instr_ae3 :
    kernel_text -∗ instr st_pc_ae3 true (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)).
  Proof. exact sti_60. Qed.

  Lemma st_instr_ae4 :
    kernel_text -∗ instr st_pc_ae4 false (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW)).
  Proof. exact sti_62. Qed.

  Lemma st_instr59 :
    kernel_text -∗ instr st_pc59 false (JAL (sjimm59, Regidx ti_ra)).
  Proof. exact sti_66. Qed.

  Lemma st_instr60 :
    kernel_text -∗ instr st_pc60 false (CSRReg (ExecCommon.csr_csrr, zreg, Regidx ti_a5, CSRRS)).
  Proof. exact sti_6a. Qed.

  Lemma st_instr61 :
    kernel_text -∗ instr st_pc61 true (ADDIW (sign_extend' 12 si61, Regidx ti_a5, Regidx ti_a5)).
  Proof. exact sti_6e. Qed.

  Lemma st_instr62 :
    kernel_text -∗ instr st_pc62 true (RTYPE (Regidx ti_a5, Regidx cli_rs1, Regidx st_tp, ADD)).
  Proof. exact sti_70. Qed.

  Lemma st_instr63 :
    kernel_text -∗ instr st_pc63 false (MRET tt).
  Proof. exact sti_72. Qed.

End WpStartInstr.
