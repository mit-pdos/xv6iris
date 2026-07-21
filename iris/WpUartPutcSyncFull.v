(* WpUartPutcSyncFull.v -- the prologue/epilogue frame handling for
   uartputc_sync, on top of the body [wp_uartputc_body] (WpUartPutcSync.v),
   assembled into the whole-function WP [wp_uartputc].

   The prologue's three stack STORES (c.sdsp) and the epilogue's three stack
   LOADS (c.ldsp) have only [_scfg] (smode_config) leaves, so they are run
   through the VCgen (VcGenS.v) as [vop_s] blocks -- exactly as WpMycpu.v runs
   its prologue/epilogue.  The three instructions that are neither ordinary
   value-ALU ops nor stack-slot VCgen ops are handled by dedicated [_scfg]
   leaves (each threads the same [smode_config] bundle):
     - c.mv  s1,a0     (0x96c) : [wp_cmv_gpr_s_config_scfg_pt] (WpSmodeRtype)
     - c.addi16sp sp,32 (0x9ae): [wp_caddi16sp_gpr_s_pt]       (WpSmodeGpr; +32
       is out of c.addi's range so it cannot be folded into the VCgen block)
     - c.ret           (0x9b0) : [wp_cret_s_zca_scfg_pt]       (WpSmodeJalr) *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import InstrBytes.
Require Import WpRvcBridge KernelText StackOwn.
Require Import WpGpr.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SRegime.
Require Import SmodeCore.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import VcGen VcGenS.
Require Import CalleeSaved.
Require Import WpUart.
Require Import WpUartPutcSync.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KptTree.
Require Import WpSmodePtLeaves WpSmodePtAlu WpSmodePtCtl.
Import Defs.

Notation UPS := KernelSyms.uartputc_sync.

(* ===================================================================== *)
(*  Decode facts for the three "structural" RVC instructions that are not  *)
(*  in the device-core / panic-check set.  (c.ret reuses [mdec_cf0].)      *)
(* ===================================================================== *)

(* 0x96c  84aa  c.mv s1,a0 *)
Lemma uprvc_84aa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x84aa : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x9ae  6105  c.addi16sp sp,32 *)
Lemma uprvc_6105 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6105 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 2), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* The prologue's [c.addi sp,-32] then the epilogue's [c.addi16sp sp,32]
   restore sp exactly.  Proved abstractly in [X] (mirror of [mycpu_frame_cancel]);
   the only [vm_compute]s are on the two CONCRETE 64-bit offsets, never on the
   symbolic base [X] -- keeping this out of the whole-function proof's final
   goal (where [X] would be an opaque [gpr_file] lookup and [vm_compute] over it
   diverges). *)
Lemma ups_frame_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64)
             = 18446744073709551584) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64)
             = 32) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551584 + 32) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

Section WpUartPutcSyncFull.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ}.
  Context `{CID : CpuId}.

  (* [instr]-builder templates, copied verbatim from WpUartPutcSync.v. *)
  (* --- [instr] facts for the three structural RVC instructions --- *)
  Lemma upi_0a : kernel_text -∗ instr (mword_of_int (UPS + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (UPS + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (UPS + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) uprvc_84aa exec_execute_C_MV. Qed.

  Lemma upi_4c : kernel_text -∗ instr (mword_of_int (UPS + 0x4c) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2), sp, sp, ADDI)).
  Proof. mk_rvc (UPS + 0x4c)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (UPS + 0x4c) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2), sp, sp, ADDI)) uprvc_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma upi_4e : kernel_text -∗ instr (mword_of_int (UPS + 0x4e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (UPS + 0x4e)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (UPS + 0x4e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

  (* --- prologue frame [instr] facts (0x00 c.addi · 0x02/04/06 sd · 0x08 addi4spn) --- *)
  Lemma upi_00 : kernel_text -∗ instr (mword_of_int (UPS + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (UPS + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (UPS + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) podec_00 exec_execute_C_ADDI. Qed.

  Lemma upi_02 : kernel_text -∗ instr (mword_of_int (UPS + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (UPS + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (UPS + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) podec_02 exec_execute_C_SDSP. Qed.

  Lemma upi_04 : kernel_text -∗ instr (mword_of_int (UPS + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (UPS + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (UPS + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) podec_04 exec_execute_C_SDSP. Qed.

  Lemma upi_06 : kernel_text -∗ instr (mword_of_int (UPS + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (UPS + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (UPS + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) podec_06 exec_execute_C_SDSP. Qed.

  Lemma upi_08 : kernel_text -∗ instr (mword_of_int (UPS + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (UPS + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (UPS + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) podec_08 exec_execute_C_ADDI4SPN. Qed.

  (* --- epilogue frame [instr] facts (0x46/48/4a ld) --- *)
  Lemma upi_46 : kernel_text -∗ instr (mword_of_int (UPS + 0x46) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (UPS + 0x46)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (UPS + 0x46) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) podec_22 exec_execute_C_LDSP. Qed.

  Lemma upi_48 : kernel_text -∗ instr (mword_of_int (UPS + 0x48) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (UPS + 0x48)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (UPS + 0x48) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) podec_24 exec_execute_C_LDSP. Qed.

  Lemma upi_4a : kernel_text -∗ instr (mword_of_int (UPS + 0x4a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (UPS + 0x4a)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (UPS + 0x4a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) podec_26 exec_execute_C_LDSP. Qed.

  (* ===================================================================== *)
  (*  Local three-slot frame elim/intro (the library ships only the         *)
  (*  one- and two-slot forms; building them here avoids re-staling the      *)
  (*  whole WP stack by editing StackOwn.v).                                 *)
  (* ===================================================================== *)
  Lemma stack_own_3_elim (sp0 : Arch.pa) :
    stack_own sp0 3 ⊢ ∃ w1 w2 w3 : bv 64,
      word_pointsto (pa_stk sp0 1) (DfracOwn 1) w1 ∗
      word_pointsto (pa_stk sp0 2) (DfracOwn 1) w2 ∗
      word_pointsto (pa_stk sp0 3) (DfracOwn 1) w3.
  Proof.
    rewrite (stack_own_app sp0 1 2) stack_own_1.
    iIntros "[H1 H23]". iDestruct "H1" as (w1) "H1".
    iDestruct (stack_own_2_elim with "H23") as (w2 w3) "[H2 H3]".
    rewrite (pa_stk_assoc sp0 1 1) (pa_stk_assoc sp0 1 2).
    iExists w1, w2, w3. iFrame.
  Qed.

  Lemma stack_own_3_intro (sp0 : Arch.pa) (w1 w2 w3 : bv 64) :
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) w1 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) w2 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) w3 -∗
    stack_own sp0 3.
  Proof.
    iIntros "H1 H2 H3". rewrite (stack_own_app sp0 1 2). iSplitL "H1".
    - by iApply stack_own_1_intro.
    - rewrite -(pa_stk_assoc sp0 1 1) -(pa_stk_assoc sp0 1 2).
      iApply (stack_own_2_intro with "H2 H3").
  Qed.

  Local Open Scope Z_scope.

  (* ------------------------------------------------------------------- *)
  (* Prologue 0x962..0x96a as a VCgen block (the c.mv s1,a0 at 0x96c is    *)
  (* NOT a vop_s -- handled by [wp_cmv_gpr_s_config_pt] after the block):     *)
  (*   c.addi  sp,-32   ·  sd ra,24(sp) · sd s0,16(sp) · sd s1,8(sp)       *)
  (*   · c.addi4spn s0,sp,32                                                *)
  (* ------------------------------------------------------------------- *)
  Definition ups_prologue : list vop_s :=
    [ VScaddi (mword_of_int 32) csp_rs1;                                  (* c.addi sp,-32   *)
      VScsdsp (mword_of_int 3) (mword_of_int 1);                          (* sd ra,24(sp)    *)
      VScsdsp (mword_of_int 2) (mword_of_int 8);                          (* sd s0,16(sp)    *)
      VScsdsp (mword_of_int 1) (mword_of_int 9);                          (* sd s1,8(sp)     *)
      VScaddi4spn (Cregidx (mword_of_int 0)) (mword_of_int 8)
                  (mword_of_int 8) ].                                     (* addi s0,sp,32   *)

  (* the three saved slots, at OLD-sp -8 / -16 / -24 (= NEW-sp +24/+16/+8) *)
  Definition ups_pro_heap0 : list (sval * sval) :=
    [ (SX 2 (wrap64 (-8)),  SX 33 0);
      (SX 2 (wrap64 (-16)), SX 34 0);
      (SX 2 (wrap64 (-24)), SX 35 0) ].
  Definition ups_pro_heap1 : list (sval * sval) :=
    [ (SX 2 (wrap64 (-8)),  SX 1 0);
      (SX 2 (wrap64 (-16)), SX 8 0);
      (SX 2 (wrap64 (-24)), SX 9 0) ].
  Definition ups_pro_regs1 : gmap regidx sval :=
    <[Regidx (mword_of_int 8 : mword 5) := SX 2 0]>
      (<[Regidx csp_rs1 := SX 2 (wrap64 (-32))]> vregs_init).

  Lemma ups_prologue_run :
    vc_block_s (VSt UPS vregs_init ups_pro_heap0 []) ups_prologue
    = Some (VSt (UPS + 10) ups_pro_regs1 ups_pro_heap1 []).
  Proof. vm_compute. reflexivity. Qed.

  (* ------------------------------------------------------------------- *)
  (* Epilogue 0x9a8..0x9ac as a VCgen block (the c.addi16sp sp,32 at 0x9ae *)
  (* is NOT a vop_s -- +32 exceeds c.addi's range; the ret at 0x9b0 is a    *)
  (* leaf too):  ld ra,24(sp) · ld s0,16(sp) · ld s1,8(sp)                  *)
  (* ------------------------------------------------------------------- *)
  Definition ups_epilogue : list vop_s :=
    [ VScldsp (mword_of_int 3) (mword_of_int 1);                          (* ld ra,24(sp)    *)
      VScldsp (mword_of_int 2) (mword_of_int 8);                          (* ld s0,16(sp)    *)
      VScldsp (mword_of_int 1) (mword_of_int 9) ].                        (* ld s1,8(sp)     *)

  (* the epilogue runs with sp already decremented; the slots sit at
     CURRENT-sp +24/+16/+8. *)
  Definition ups_epi_heap : list (sval * sval) :=
    [ (SX 2 24, SX 33 0);
      (SX 2 16, SX 34 0);
      (SX 2 8,  SX 35 0) ].
  Definition ups_epi_regs1 : gmap regidx sval :=
    <[Regidx (mword_of_int 9 : mword 5) := SX 35 0]>
      (<[Regidx (mword_of_int 8 : mword 5) := SX 34 0]>
         (<[Regidx (mword_of_int 1 : mword 5) := SX 33 0]> vregs_init)).

  Lemma ups_epilogue_run :
    vc_block_s (VSt (UPS + 0x46) vregs_init ups_epi_heap []) ups_epilogue
    = Some (VSt (UPS + 0x46 + 6) ups_epi_regs1 ups_epi_heap []).
  Proof. vm_compute. reflexivity. Qed.

  (* the prologue's / epilogue's block_instrs, from kernel_text. *)
  Lemma ups_prologue_instrs :
    kernel_text -∗ block_instrs_s UPS ups_prologue.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s ups_prologue vop_s_ast].
    replace (UPS + 2 + 2) with (UPS + 4) by lia.
    replace (UPS + 4 + 2) with (UPS + 6) by lia.
    replace (UPS + 6 + 2) with (UPS + 8) by lia.
    iSplitR; [by iApply upi_00|].
    iSplitR; [by iApply upi_02|].
    iSplitR; [by iApply upi_04|].
    iSplitR; [by iApply upi_06|].
    iSplitR.
    { assert (Hcreg : creg2reg_idx (Cregidx (mword_of_int 0 : mword 3))
                      = Regidx (mword_of_int 8 : mword 5))
        by (vm_compute; reflexivity).
      rewrite -Hcreg. by iApply upi_08. }
    done.
  Qed.

  Lemma ups_epilogue_instrs :
    kernel_text -∗ block_instrs_s (UPS + 0x46) ups_epilogue.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s ups_epilogue vop_s_ast].
    replace (UPS + 0x46 + 2) with (UPS + 0x48) by lia.
    replace (UPS + 0x48 + 2) with (UPS + 0x4a) by lia.
    iSplitR; [by iApply upi_46|].
    iSplitR; [by iApply upi_48|].
    iSplitR; [by iApply upi_4a|].
    done.
  Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the ENTIRE uartputc_sync, entry (0x80000962)  *)
  (*  through its return to the caller (PC = ra with the low bit cleared). *)
  (*  Registers: ra=x1 sp=x2 s0=x8 s1=x9 a0=x10.  The panic path taken is   *)
  (*  panicking != 0 && panicked == 0 (so no push_off/pop_off, no infinite  *)
  (*  spin); the UART is THRE-ready so the wait loop exits immediately and   *)
  (*  the low byte of the char [a0] is written to THR.                      *)
  (*  On exit every callee-saved register holds its entry value             *)
  (*  ([callee_saved m0 mf]: sp/tp/s0/s1/s2..s11 -- sp/s0/s1 by way of the   *)
  (*  32-byte stack frame, the rest because nothing on the path writes       *)
  (*  them), and so does ra, which the frame also saves and restores.        *)
  (* =================================================================== *)
  (* [gpr_matches] from the [vregs_den] equality (the block runner's entry
     interface wants the former; my ρ setup proves the latter). *)
  Lemma gpr_matches_of_den (ρ : nat -> mword 64) (vr : gmap regidx sval)
      (m : regfile) :
    vregs_den ρ vr = m -> gpr_matches ρ vr m.
  Proof.
    intros <- r sv Hr. exact (vregs_den_lookup ρ vr r sv Hr).
  Qed.

End WpUartPutcSyncFull.
