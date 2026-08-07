(* CodeTimerinitAux.v -- timerinit()'s operand vocabulary, over the GENERATED
   decode layer in CodeTimerinit.v.

   The 21 [ti_instr*] facts are conversions from their generated twins
   ([Proof. exact tmi_<off>. Qed.]); the encoding words this file used to
   define are gone.  What is left -- the register indices ([ti_ra], [ti_s0],
   [ti_a4], [ti_a5], their creg forms) and the frame immediates ([i9], [u10],
   [u11], [nz12], [i28]) -- is shared with start(), which opens the same
   16-byte frame in the same registers, so CodeStartAux.v imports it.  See
   CodeEntryAux.v's header for why the conversions matter. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto.
Require Import WpMmodeLeafBase.
Require Import WpGprCsrrA WpGprCsrrB WpGprCsrwA WpGprCsrwB.
Require Import InstrBytes.
Require Import KernelText.
From iris.base_logic.lib Require Import invariants.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import CodeTimerinit.
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

(* ===================================================================== *)
(* Decode lemmas.  RVC: concrete compressed words decode through            *)
(* [rvc_oneshot] (WpRvcBridge); 32-bit: [decode_any] one-shot.             *)
(* ===================================================================== *)

(* ---- idx 9: 0x1141 -> c.addi sp, -16 ---- *)

(* ---- idx 10: 0xe406 -> c.sdsp ra, 8(sp) ---- *)

(* ---- idx 11: 0xe022 -> c.sdsp s0, 0(sp) ---- *)

(* ---- idx 12: 0x0800 -> c.addi4spn s0, sp, 16 ---- *)

(* ---- idx 14: 0x577d -> c.li a4, -1 ---- *)

(* ---- idx 15: 0x177e -> c.slli a4, 63 ---- *)

(* ---- idx 16: 0x8fd9 -> c.or a5, a4 ---- *)

(* ---- idx 24: 0x97ba -> c.add a5, a4 ---- *)

(* ---- idx 26: 0x60a2 -> c.ldsp ra, 8(sp) ---- *)

(* ---- idx 27: 0x6402 -> c.ldsp s0, 0(sp) ---- *)

(* ---- idx 28: 0x0141 -> c.addi sp, 16 ---- *)

(* ---- idx 29: 0x8082 -> c.ret = c.jr ra ---- *)

(* ---- the nine 32-bit instructions: one-shot [decode_any] ---- *)









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
  Context `{GEN : GenId} `{CID : CpuId}.

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
  Proof. exact tmi_00. Qed.

  Lemma ti_instr10 :
    kernel_text -∗ instr ti_pc10 true (STORE (zero_extend' 12 (concat_vec u10 ('b"000")), Regidx ti_ra, Regidx csp_rs1, 8)).
  Proof. exact tmi_02. Qed.

  Lemma ti_instr11 :
    kernel_text -∗ instr ti_pc11 true (STORE (zero_extend' 12 (concat_vec u11 ('b"000")), Regidx ti_s0, Regidx csp_rs1, 8)).
  Proof. exact tmi_04. Qed.

  Lemma ti_instr12 :
    kernel_text -∗ instr ti_pc12 true (ITYPE (caddi4spn_imm nz12, Regidx csp_rs1, Regidx ti_s0, ADDI)).
  Proof. exact tmi_06. Qed.

  Lemma ti_instr13 :
    kernel_text -∗ instr ti_pc13 false (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS)).
  Proof. exact tmi_08. Qed.

  Lemma ti_instr14 :
    kernel_text -∗ instr ti_pc14 true (ITYPE (sign_extend' 12 i14, Regidx cli_rs1, Regidx ti_a4, ADDI)).
  Proof. exact tmi_0c. Qed.

  Lemma ti_instr15 :
    kernel_text -∗ instr ti_pc15 true (SHIFTIOP (sh15, Regidx ti_a4, Regidx ti_a4, SLLI)).
  Proof. exact tmi_0e. Qed.

  Lemma ti_instr16 :
    kernel_text -∗ instr ti_pc16 true (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)).
  Proof. exact tmi_10. Qed.

  Lemma ti_instr17 :
    kernel_text -∗ instr ti_pc17 false (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW)).
  Proof. exact tmi_12. Qed.

  Lemma ti_instr18 :
    kernel_text -∗ instr ti_pc18 false (CSRReg (WpGprCsrrA.csr_mcounteren, zreg, Regidx ti_a5, CSRRS)).
  Proof. exact tmi_16. Qed.

  Lemma ti_instr19 :
    kernel_text -∗ instr ti_pc19 false (ITYPE (i19, Regidx ti_a5, Regidx ti_a5, ORI)).
  Proof. exact tmi_1a. Qed.

  Lemma ti_instr20 :
    kernel_text -∗ instr ti_pc20 false (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx ti_a5, zreg, CSRRW)).
  Proof. exact tmi_1e. Qed.

  Lemma ti_instr21 :
    kernel_text -∗ instr ti_pc21 false (CSRReg (WpGprCsrrB.csr_time, zreg, Regidx ti_a5, CSRRS)).
  Proof. exact tmi_22. Qed.

  Lemma ti_instr22 :
    kernel_text -∗ instr ti_pc22 false (UTYPE (i22, Regidx ti_a4, LUI)).
  Proof. exact tmi_26. Qed.

  Lemma ti_instr23 :
    kernel_text -∗ instr ti_pc23 false (ITYPE (i23, Regidx ti_a4, Regidx ti_a4, ADDI)).
  Proof. exact tmi_2a. Qed.

  Lemma ti_instr24 :
    kernel_text -∗ instr ti_pc24 true (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, ADD)).
  Proof. exact tmi_2e. Qed.

  Lemma ti_instr25 :
    kernel_text -∗ instr ti_pc25 false (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx ti_a5, zreg, CSRRW)).
  Proof. exact tmi_30. Qed.

  Lemma ti_instr26 :
    kernel_text -∗ instr ti_pc26 true (LOAD (zero_extend' 12 (concat_vec u10 ('b"000")), Regidx csp_rs1, Regidx ti_ra, false, 8)).
  Proof. exact tmi_34. Qed.

  Lemma ti_instr27 :
    kernel_text -∗ instr ti_pc27 true (LOAD (zero_extend' 12 (concat_vec u11 ('b"000")), Regidx csp_rs1, Regidx ti_s0, false, 8)).
  Proof. exact tmi_36. Qed.

  Lemma ti_instr28 :
    kernel_text -∗ instr ti_pc28 true (ITYPE (sign_extend' 12 i28, Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. exact tmi_38. Qed.

  Lemma ti_instr29 :
    kernel_text -∗ instr ti_pc29 true (JALR (zeros' 12, Regidx ti_ra, zreg)).
  Proof. exact tmi_3a. Qed.

End WpTimerinit.
