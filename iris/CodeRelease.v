(* CodeRelease.v -- whole-function WP for xv6's release() in S-mode, against
   the CSL lock invariant of WpLock.v: the caller supplies [is_lock γ lk R],
   the ownership token [locked γ] and the protected resource [R]; release()
   stores them back into the invariant when its [sw zero,0(s1)] clears the
   lock word (WpLockLeaves.wp_sw_zero_lockinv_pt).

     release @ 0x80000c82 (KernelInstrs.kernel_bytes):
       +0x00 1101      c.addi sp,-32
       +0x02 ec06      c.sdsp ra,24(sp)
       +0x04 e822      c.sdsp s0,16(sp)
       +0x06 e426      c.sdsp s1,8(sp)
       +0x08 1000      c.addi4spn s0,sp,32
       +0x0a 84aa      c.mv s1,a0
       +0x0c f07ff0ef  jal ra,holding      returns 1 (the token refutes 0)
       +0x10 cd11      c.beqz a0,+0x1c     NOT taken
       +0x12 0004b823  sd zero,16(s1)      lk->cpu := 0
       +0x16 0310000f  fence rw,w
       +0x1a 0004a023  sw zero,0(s1)       lk->locked := 0  (invariant closes)
       +0x1e f9bff0ef  jal ra,pop_off
       +0x22 60e2 / +0x24 6442 / +0x26 64a2 / +0x28 6105 / +0x2a 8082  epilogue *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode KernelText.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KernelRvcDecode.
Require Import KernelBaseDecode.
Require Import WpLock CodePopOff.
(* subrange_full / mSIE_lower / sie_bit for the sstatus-SIE bridge; kept
   QUALIFIED so the WpGprCsrwC namespace doesn't shadow anything. *)
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode lemmas.                                                         *)
(* ===================================================================== *)

Local Ltac rl_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac rl_dbase s Hpriv :=
  decode_pause_prefix s Hpriv;
  match goal with |- ?lhs = ?rhs =>
    let l := eval vm_compute in lhs in change_no_check (l = rhs) end;
  rl_ast.

(* +0x0c  0xf07ff0ef  jal ra,holding (offset -0xfa) *)
Lemma rldec_jal_holding s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf07ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fff06 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; rl_dbase s Hpriv ]. Qed.

(* +0x1e  0xf9bff0ef  jal ra,pop_off (offset -0x66) *)
Lemma rldec_jal_popoff s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf9bff0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fff9a : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; rl_dbase s Hpriv ]. Qed.

(* +0x12  0x0004b823  sd zero,16(s1) *)
Lemma rldec_sd_zero s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0004b823 : mword 32)) s
  = Some (STORE (mword_of_int 16, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; rl_dbase s Hpriv ]. Qed.

(* ===================================================================== *)
(* [instr] facts.                                                         *)
(* ===================================================================== *)
Section WpReleaseInstr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Lemma rli_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.release + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (KernelSyms.release + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma rli_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.release + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KernelSyms.release + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma rli_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.release + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (KernelSyms.release + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma rli_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.release + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KernelSyms.release + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma rli_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.release + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (KernelSyms.release + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma rli_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.release + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (KernelSyms.release + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma rli_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x0c) : mword 64) false (JAL (mword_of_int 0x1fff06 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.release + 0x0c)%Z (mword_of_int 0xf07ff0ef : mword 32)
    (mword_of_int (KernelSyms.release + 0x0c) : mword 64) (JAL (mword_of_int 0x1fff06 : mword 21, Regidx (mword_of_int 1))) rldec_jal_holding. Qed.

  Lemma rli_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x10) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (KernelSyms.release + 0x10)%Z (mword_of_int 0xcd11 : mword 16)
    (mword_of_int (KernelSyms.release + 0x10) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) cdec_cd11 exec_execute_C_BEQZ. Qed.

  Lemma rli_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x12) : mword 64) false (STORE (mword_of_int 16, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8)).
  Proof. mk_base (KernelSyms.release + 0x12)%Z (mword_of_int 0x0004b823 : mword 32)
    (mword_of_int (KernelSyms.release + 0x12) : mword 64) (STORE (mword_of_int 16, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8)) rldec_sd_zero. Qed.

  Lemma rli_16 : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x16) : mword 64) false (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))).
  Proof. mk_base (KernelSyms.release + 0x16)%Z (mword_of_int 0x0310000f : mword 32)
    (mword_of_int (KernelSyms.release + 0x16) : mword 64) (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))) ppdec_fence. Qed.

  Lemma rli_1a : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x1a) : mword 64) false (STORE (mword_of_int 0, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (KernelSyms.release + 0x1a)%Z (mword_of_int 0x0004a023 : mword 32)
    (mword_of_int (KernelSyms.release + 0x1a) : mword 64) (STORE (mword_of_int 0, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)) bdec_0004a023. Qed.

  Lemma rli_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x1e) : mword 64) false (JAL (mword_of_int 0x1fff9a : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.release + 0x1e)%Z (mword_of_int 0xf9bff0ef : mword 32)
    (mword_of_int (KernelSyms.release + 0x1e) : mword 64) (JAL (mword_of_int 0x1fff9a : mword 21, Regidx (mword_of_int 1))) rldec_jal_popoff. Qed.

  Lemma rli_22 : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x22) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.release + 0x22)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (KernelSyms.release + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma rli_24 : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x24) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.release + 0x24)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (KernelSyms.release + 0x24) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma rli_26 : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x26) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.release + 0x26)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (KernelSyms.release + 0x26) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma rli_28 : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x28) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.release + 0x28)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (KernelSyms.release + 0x28) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma rli_2a : kernel_text -∗ instr (mword_of_int (KernelSyms.release + 0x2a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.release + 0x2a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.release + 0x2a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End WpReleaseInstr.

(* ===================================================================== *)
(* JAL with a 2-mod-4 target, legal under Zca (pop_off sits at 0x...c3a). *)
(* ===================================================================== *)


Section WpJalZca.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


End WpJalZca.

(* ===================================================================== *)
(* Bridge: SIE=0 on mstatus ==> pop_off's sstatus SIE-bit precondition.    *)
(* Lets wp_release/callers derive the [neq_vec (and_vec (sstatus_read      *)
(* mstatus0) 2) zero_reg = false] pop_off premise from the SIE=0 fact that  *)
(* now lives folded inside smode_config (so mstatus0 stays hidden).        *)
(* ===================================================================== *)
(* [mword1_zero_of_ne_one] is a pure bitvector fact -- now in RiscvExtras. *)


(* ===================================================================== *)
(* wp_release -- the CSL release spec: the caller supplies the lock       *)
(* [is_lock γ lka R], the ownership token [locked γ] and the protected    *)
(* resource [R]; both are returned INTO the invariant by the lock-word    *)
(* clear.  Requires lk->cpu = mycpu() (so holding() returns 1), plus      *)
(* pop_off()'s preconditions (SIE = 0, noff >= 1, intena = 0).            *)
(* ===================================================================== *)
Section WpReleaseTop.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* ===== [smode_config] leaf wrappers release's body needs ===== *)









End WpReleaseTop.
