(* WpPushOffTop.v -- the top-level WP for xv6's push_off() in S-mode.
   Composes: the prologue/epilogue stack ops, csrrci (interrupt disable,
   WpPushOffCsr), the two mycpu() calls (WpMycpu), the per-cpu noff/intena
   4-byte accesses (WpPushOffMem), the beqz two-arm join, and the new
   arithmetic/branch instruction lemmas (WpPushOff).  Full functional
   postcondition: SIE cleared, noff incremented, intena = old SIE iff noff
   was 0, callee-saved restored, return to caller. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
From iris.base_logic.lib Require Import ghost_var.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode ExecCommon KernelText.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import WpPushOffCsr.
Require Import WpRvcBridge KernelRvcDecode.
(* QUALIFIED (no Import): sstatus SIE-bit bridges for the saved-intena = 0 fact. *)
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Export WpSmodeLeafBase.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode templates (mirrors of WpMycpu / WpTimerinit / WpKvInstr).       *)
(* ===================================================================== *)
Local Ltac po_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac po_close1 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; po_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

Local Ltac po_close_ld s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (Defs.and_boolM (returnM _)
                          (currentlyEnabled Ext_Zca))) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; po_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

Local Ltac po_close0 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; po_ast
  | apply (exec_currentlyEnabled_Zca s HmisaC) ].

(* ---- RVC decodes ---- *)

(* cdec_5d3c (c.lw a5,120(a0)) is shared with pop_off — now in KernelRvcDecode. *)

(* +0x16  0xcb99  c.beqz a5,80000bec *)
Lemma podec_16 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcb99 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 11, Cregidx (mword_of_int 7)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* 0x2785 (c.addiw a5,a5,1) is shared with clockintr and filedup -- now
   cdec_2785 in KernelRvcDecode. *)

(* cdec_dd3c (c.sw a5,120(a0)) is shared with pop_off — now in KernelRvcDecode. *)

(* +0x36  0xdd7c  c.sw a5,124(a0) *)
Lemma podec_sw124 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xdd7c : mword 16)) s
  = Some (C_SW (mword_of_int 31, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x38  0xb7c5  c.j 80000bd8 *)
(* [cdec_b7c5] -- shared, see KernelRvcDecode.v *)

(* ---- base (4-byte) decodes ----
   [decode_any]'s final [reflexivity] fails here: [vm_compute] reduces BOTH
   sides to [@BV] literals whose [BvWf] proof fields differ (proof-irrelevant
   but not definitionally equal).  Reduce only the LHS, then close each bv leaf
   with [bv_eq] (value-only). *)
Local Ltac po_dbase s Hpriv :=
  decode_pause_prefix s Hpriv;
  match goal with |- ?lhs = ?rhs =>
    let l := eval vm_compute in lhs in change_no_check (l = rhs) end;
  po_ast.

(* +0x0a  0x100177f3  csrrci a5,sstatus,2 *)
Lemma podec_0a s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x100177f3 : mword 32)) s
  = Some (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 15), CSRRC), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; po_dbase s Hpriv ]. Qed.

(* +0x10  0x507000ef  jal ra,mycpu *)
Lemma podec_10 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x507000ef : mword 32)) s
  = Some (JAL (mword_of_int 0xd06 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; po_dbase s Hpriv ]. Qed.

(* +0x18  0x4ff000ef  jal ra,mycpu *)
Lemma podec_18 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4ff000ef : mword 32)) s
  = Some (JAL (mword_of_int 0xcfe : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; po_dbase s Hpriv ]. Qed.

(* +0x2c  0x4eb000ef  jal ra,mycpu *)
Lemma podec_2c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4eb000ef : mword 32)) s
  = Some (JAL (mword_of_int 0xcea : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; po_dbase s Hpriv ]. Qed.

(* +0x30  0x0014d793  srli a5,s1,1 *)
Lemma podec_30 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0014d793 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 1 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 15), SRLI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; po_dbase s Hpriv ]. Qed.

(* ===================================================================== *)
(* poexec_lw/poexec_sw120 are shared with pop_off and live in
   KernelRvcDecode; poexec_sw124 below is push_off's own slot.  Every one of
   these is a one-line instance of WpMmodeLeafBase's [exec_execute_C_*_leaf]
   bridge -- do not hand-roll the creg/immediate reduction again. *)
Lemma poexec_sw124 s :
  exec (execute (C_SW (mword_of_int 31, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 124, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma poexec_andi s :
  exec (execute (C_ANDI (mword_of_int 1, Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)), s).
Proof. apply exec_execute_C_ANDI_leaf; vm_compute; reflexivity. Qed.


(* named form of wp_mycpu's output register file (= call_mycpu's m11 chain),
   so downstream geometry can reference its a0/sp lookups. *)
(* po_addv_assoc (add_vec associativity) is shared with pop_off — now in KernelRvcDecode. *)


(* ===================================================================== *)
(* SIE=0 (folded into smode_config) collapses push_off's saved-interrupt   *)
(* store [storeval32] to the concrete [zeros' 32], so wp_push_off's intena  *)
(* postcondition needs no mstatus0.  Bridges mirror WpAcquireLock.          *)
(* ===================================================================== *)




Section WpPushOffTop.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the push_off instructions from [kernel_text].      *)
  (* ------------------------------------------------------------------- *)
  Notation PO := KernelSyms.push_off.

  Lemma poi_00 : kernel_text -∗ instr (mword_of_int (PO + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PO + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (PO + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma poi_02 : kernel_text -∗ instr (mword_of_int (PO + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PO + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (PO + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma poi_04 : kernel_text -∗ instr (mword_of_int (PO + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PO + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (PO + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma poi_06 : kernel_text -∗ instr (mword_of_int (PO + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (PO + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (PO + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma poi_08 : kernel_text -∗ instr (mword_of_int (PO + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PO + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (PO + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma poi_0a : kernel_text -∗ instr (mword_of_int (PO + 0x0a) : mword 64) false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 15), CSRRC)).
  Proof. mk_base (PO + 0x0a)%Z (mword_of_int 0x100177f3 : mword 32)
    (mword_of_int (PO + 0x0a) : mword 64) (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 15), CSRRC)) podec_0a. Qed.

  Lemma poi_0e : kernel_text -∗ instr (mword_of_int (PO + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (PO + 0x0e)%Z (mword_of_int 0x84be : mword 16)
    (mword_of_int (PO + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)) cdec_84be exec_execute_C_MV. Qed.

  Lemma poi_10 : kernel_text -∗ instr (mword_of_int (PO + 0x10) : mword 64) false (JAL (mword_of_int 0xd06 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PO + 0x10)%Z (mword_of_int 0x507000ef : mword 32)
    (mword_of_int (PO + 0x10) : mword 64) (JAL (mword_of_int 0xd06 : mword 21, Regidx (mword_of_int 1))) podec_10. Qed.

  Lemma poi_14 : kernel_text -∗ instr (mword_of_int (PO + 0x14) : mword 64) true (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (PO + 0x14)%Z (mword_of_int 0x5d3c : mword 16)
    (mword_of_int (PO + 0x14) : mword 64) (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) cdec_5d3c poexec_lw. Qed.

  Lemma poi_16 : kernel_text -∗ instr (mword_of_int (PO + 0x16) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (PO + 0x16)%Z (mword_of_int 0xcb99 : mword 16)
    (mword_of_int (PO + 0x16) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) podec_16 exec_execute_C_BEQZ. Qed.

  Lemma poi_18 : kernel_text -∗ instr (mword_of_int (PO + 0x18) : mword 64) false (JAL (mword_of_int 0xcfe : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PO + 0x18)%Z (mword_of_int 0x4ff000ef : mword 32)
    (mword_of_int (PO + 0x18) : mword 64) (JAL (mword_of_int 0xcfe : mword 21, Regidx (mword_of_int 1))) podec_18. Qed.

  Lemma poi_1c : kernel_text -∗ instr (mword_of_int (PO + 0x1c) : mword 64) true (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (PO + 0x1c)%Z (mword_of_int 0x5d3c : mword 16)
    (mword_of_int (PO + 0x1c) : mword 64) (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) cdec_5d3c poexec_lw. Qed.

  Lemma poi_1e : kernel_text -∗ instr (mword_of_int (PO + 0x1e) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (PO + 0x1e)%Z (mword_of_int 0x2785 : mword 16)
    (mword_of_int (PO + 0x1e) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2785 exec_execute_C_ADDIW. Qed.

  Lemma poi_20 : kernel_text -∗ instr (mword_of_int (PO + 0x20) : mword 64) true (STORE (mword_of_int 120, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)).
  Proof. mk_rvc (PO + 0x20)%Z (mword_of_int 0xdd3c : mword 16)
    (mword_of_int (PO + 0x20) : mword 64) (STORE (mword_of_int 120, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)) cdec_dd3c poexec_sw120. Qed.

  Lemma poi_22 : kernel_text -∗ instr (mword_of_int (PO + 0x22) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PO + 0x22)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (PO + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma poi_24 : kernel_text -∗ instr (mword_of_int (PO + 0x24) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PO + 0x24)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (PO + 0x24) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma poi_26 : kernel_text -∗ instr (mword_of_int (PO + 0x26) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (PO + 0x26)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (PO + 0x26) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma poi_28 : kernel_text -∗ instr (mword_of_int (PO + 0x28) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (PO + 0x28)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (PO + 0x28) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma poi_2a : kernel_text -∗ instr (mword_of_int (PO + 0x2a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PO + 0x2a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PO + 0x2a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma poi_2c : kernel_text -∗ instr (mword_of_int (PO + 0x2c) : mword 64) false (JAL (mword_of_int 0xcea : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PO + 0x2c)%Z (mword_of_int 0x4eb000ef : mword 32)
    (mword_of_int (PO + 0x2c) : mword 64) (JAL (mword_of_int 0xcea : mword 21, Regidx (mword_of_int 1))) podec_2c. Qed.

  Lemma poi_30 : kernel_text -∗ instr (mword_of_int (PO + 0x30) : mword 64) false (SHIFTIOP (mword_of_int 1 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 15), SRLI)).
  Proof. mk_base (PO + 0x30)%Z (mword_of_int 0x0014d793 : mword 32)
    (mword_of_int (PO + 0x30) : mword 64) (SHIFTIOP (mword_of_int 1 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 15), SRLI)) podec_30. Qed.

  Lemma poi_34 : kernel_text -∗ instr (mword_of_int (PO + 0x34) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_rvc (PO + 0x34)%Z (mword_of_int 0x8b85 : mword 16)
    (mword_of_int (PO + 0x34) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) cdec_8b85 poexec_andi. Qed.

  Lemma poi_36 : kernel_text -∗ instr (mword_of_int (PO + 0x36) : mword 64) true (STORE (mword_of_int 124, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)).
  Proof. mk_rvc (PO + 0x36)%Z (mword_of_int 0xdd7c : mword 16)
    (mword_of_int (PO + 0x36) : mword 64) (STORE (mword_of_int 124, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)) podec_sw124 poexec_sw124. Qed.

  Lemma poi_38 : kernel_text -∗ instr (mword_of_int (PO + 0x38) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PO + 0x38)%Z (mword_of_int 0xb7c5 : mword 16)
    (mword_of_int (PO + 0x38) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")), zreg)) cdec_b7c5 exec_execute_C_J. Qed.

  (* ================================================================== *)
  (* [smode_config] wrappers for the raw leaves push_off/pop_off call,   *)
  (* so their bodies thread the bundle instead of the unbundled cells.   *)
  (* Each peels the config once and re-bundles in the continuation; the  *)
  (* instructions preserve every config cell.                            *)
  (* ================================================================== *)






  (* The reusable jal->mycpu->return composites wp_call_mycpu /
     wp_call_mycpu_scfg_cs now live in WpMycpu (beside wp_mycpu), so
     holding/acquire reuse them without depending on push_off. *)

  (* ============ the suffix from 0x80000bd8 (PO+0x18) to c.ret ============ *)



  (* ============ the full push_off, entry (0x80000bc0) to caller return ============ *)




End WpPushOffTop.
