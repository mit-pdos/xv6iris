(* CodeEntryAux.v -- what is left of the HAND-WRITTEN decode layer for _entry
   once the generated one covers it.

   [CodeEntry.v] is produced by tools/gen_code.py from the tracked dump and
   holds an [instr] fact per instruction ([eni_<off>]), with the encoding word
   and every decoded immediate spelled as literals the tool derived.  This file
   used to state all of that a second time by hand -- eight [decode_*]
   templates over its own copies of the encoding words, and fifteen empty
   Section husks of forward-exec scaffolding left behind by earlier cleanups.

   What remains is the OPERAND VOCABULARY the M-mode weakest preconditions in
   WpEntryNew.v are written in -- the pc constants, the register indices and
   immediates as bit-extractions off the four RVC/base words that carry them,
   and [entry_sp1] -- plus the eight [entry_instr_*] facts, each now a
   CONVERSION from its generated twin ([Proof. exact eni_<off>. Qed.]).

   That conversion is the point: it is a build-time check that this file's
   operand constants agree with the dump.  An upstream bump that re-encodes an
   instruction updates [CodeEntry.v] and the [exact] stops typechecking -- a
   loud failure, where a private copy of a word would just go quietly stale. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec WpDecode.
Require Import WpAuipc.
Require Import RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import InstrBytes KernelText.
From iris.base_logic.lib Require Import invariants.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec WpDecode.
Require Import WpRvcBridge.
Require Export ExecCommon.
Require Import CodeEntry.
Local Open Scope Z_scope.

(* ---- the eight instruction words, their operand fields, and their decodes ---- *)
(* ==== compressed decode: walker + decode_C_lui ==== *)

Definition rd_clui : regidx :=
  Regidx (autocast (T := mword)
            (subrange_vec_dec (subrange_vec_dec h_lui 11 7) (Z.sub regidx_bit_width 1) 0)).


(* ==== execute lemmas (generic register write) ==== *)

(* ==== generalized try_step wrapper (announce word arbitrary, for RVC) ==== *)
(* ==== add (C_ADD, RVC) ==== *)
Definition h_add : mword 16 := mword_of_int 0x912a.
Definition rsd_cadd : regidx :=
  Regidx (autocast (T := mword) (subrange_vec_dec (subrange_vec_dec h_add 11 7) (Z.sub regidx_bit_width 1) 0)).
Definition rs2_cadd : regidx :=
  Regidx (autocast (T := mword) (subrange_vec_dec (subrange_vec_dec h_add 6 2) (Z.sub regidx_bit_width 1) 0)).


(* ====================================================================== *)
(* JAL (control flow) -- the "jump to start" capstone.                     *)
(* ====================================================================== *)
Definition w_jal : mword 32 := mword_of_int 0x42000ef.
Definition i_jal : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_jal 11 7) (regidx_bit_width - 1) 0).
Definition imm_jal : mword 21 :=
  concat_vec (concat_vec (concat_vec (concat_vec
    (subrange_vec_dec w_jal 31 31) (subrange_vec_dec w_jal 19 12))
    (subrange_vec_dec w_jal 20 20)) (subrange_vec_dec w_jal 30 21)) ('b"0").


(* ====================================================================== *)
(* MUL (M-extension) -- forward_exec_mul + Ext_M currentlyEnabled tower.    *)
(* ====================================================================== *)

Definition w_mul : mword 32 := mword_of_int 0x2b50533.
Definition i_mul_rs2 : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_mul 24 20) (regidx_bit_width - 1) 0).
Definition i_mul_rs1 : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_mul 19 15) (regidx_bit_width - 1) 0).
Definition i_mul_rd : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_mul 11 7) (regidx_bit_width - 1) 0).


(* ====================================================================== *)
(* ADDI (RVC, 2-aligned) -- width-2 fetch stack + forward_exec_addi.        *)
(* ====================================================================== *)

(* ====================================================================== *)
(* Width-2 mem-read stack (mirror of the width-4 stack in RiscvFetchExec). *)
(* ====================================================================== *)

Definition h_addi : mword 16 := mword_of_int 0x585.
Definition imm_caddi : mword 6 :=
  concat_vec (subrange_vec_dec h_addi 12 12) (subrange_vec_dec h_addi 6 2).
Definition rsd_caddi : regidx :=
  Regidx (autocast (T := mword)
            (subrange_vec_dec (subrange_vec_dec h_addi 11 7) (Z.sub regidx_bit_width 1) 0)).


(* ====================================================================== *)
(* RVC 4-byte fetch SL wrapper + wp_step_lui + wp_step_add (4-aligned RVC). *)
(* ====================================================================== *)
(* ====================================================================== *)
(* wp_step_mul (4-aligned F_Base, M-ext).                                  *)
(* ====================================================================== *)

(* ====================================================================== *)
(* CSRR (csrr a1,mhartid) -- forward_exec_csrr (F_Base, fetch-agnostic).    *)
(* ====================================================================== *)


(* ====================================================================== *)
(* RVC 2-byte fetch SL wrapper + wp_step_addi (2-aligned RVC).             *)
(* ====================================================================== *)

(* ====================================================================== *)
(* wp_step_csrr (2-aligned F_Base).                                        *)
(* ====================================================================== *)

(* ====================================================================== *)
(* wp_step_jal (2-aligned F_Base, control flow -- jump to start).          *)
(* ====================================================================== *)

Section CodeEntryAux.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

(* PCs of the eight instructions. *)
Definition pc_e0 : mword 64 := mword_of_int (KernelSyms._entry).  (* AUIPC  *)
Definition pc_e1 : mword 64 := mword_of_int (KernelSyms._entry + 0x4).  (* LOAD   *)
Definition pc_e2 : mword 64 := mword_of_int (KernelSyms._entry + 0x8).  (* C.LUI  *)
Definition pc_e3 : mword 64 := mword_of_int (KernelSyms._entry + 0xa).  (* CSRRS  *)
Definition pc_e4 : mword 64 := mword_of_int (KernelSyms._entry + 0xe).  (* C.ADDI *)
Definition pc_e5 : mword 64 := mword_of_int (KernelSyms._entry + 0x10).  (* MUL    *)
Definition pc_e6 : mword 64 := mword_of_int (KernelSyms._entry + 0x14).  (* C.ADD  *)
Definition pc_e7 : mword 64 := mword_of_int (KernelSyms._entry + 0x16).  (* JAL    *)
Definition pc_start : mword 64 := mword_of_int (KernelSyms.start). (* start() *)

(* The value AUIPC writes to sp (= pc0 + (imm_auipc<<12) = 0x8000a000). *)
Definition entry_sp1 : mword 64 := add_vec pc_e0 (auipc_off imm_auipc).
Lemma entry_instr_auipc :
  kernel_text -∗ instr pc_e0 false (UTYPE (imm_auipc, Regidx i_auipc, AUIPC)).
Proof. exact eni_00. Qed.
Lemma entry_instr_ld :
  kernel_text -∗ instr pc_e1 false (LOAD (imm_ld, Regidx i_ld, Regidx i_ld, false, 8)).
Proof. exact eni_04. Qed.
Lemma entry_instr_clui :
  kernel_text -∗ instr pc_e2 true (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI)).
Proof. exact eni_08. Qed.
Lemma entry_instr_csrr :
  kernel_text -∗ instr pc_e3 false (CSRReg (csr_csrr, zreg, Regidx i_rd_csrr, CSRRS)).
Proof. exact eni_0a. Qed.
Lemma entry_instr_caddi :
  kernel_text -∗ instr pc_e4 true (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI)).
Proof. exact eni_0e. Qed.
Lemma entry_instr_mul :
  kernel_text -∗
  instr pc_e5 false (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd, mulop_mul)).
Proof. exact eni_10. Qed.
Lemma entry_instr_cadd :
  kernel_text -∗ instr pc_e6 true (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD)).
Proof. exact eni_14. Qed.
Lemma entry_instr_jal :
  kernel_text -∗ instr pc_e7 false (JAL (imm_jal, Regidx i_jal)).
Proof. exact eni_16. Qed.

End CodeEntryAux.
